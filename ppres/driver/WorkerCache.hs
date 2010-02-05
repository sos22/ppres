{- This module is intended to hide all the grubbiness of the interface
   to the C world, and provides a nice functional API to it.  The
   functional API is expressed entirely in terms of Histories, and we
   are responsible for mapping them into Workers as and when
   necessary. -}
module WorkerCache(initWorkerCache, destroyWorkerCache, run,
                   trace, traceThread, traceAddress, runMemory,
                   threadState, replayState, controlTrace,
                   fetchMemory, vgIntermediate, nextThread) where

import Data.Word
import Control.Monad.State
import Data.IORef
import Random
import Control.Exception
import qualified Debug.Trace

import System.IO.Unsafe

import Types
import Worker
import History

dt :: String -> a -> a
dt = const id

data CacheGeneration = CacheGeneration { cg_max_size :: Int,
                                         cg_workers :: IORef [(History, Worker)],
                                         cg_parent :: Maybe CacheGeneration }

data WorkerCache = WorkerCache { wc_cache :: CacheGeneration,
                                 wc_start :: Worker }


globalWorkerCache :: IORef (Maybe WorkerCache)
{-# NOINLINE globalWorkerCache #-}
globalWorkerCache =
    unsafePerformIO $ newIORef Nothing

workerCache :: IO WorkerCache
workerCache =
    do wc <- readIORef globalWorkerCache
       case wc of
         Nothing -> error "worker cache not ready"
         Just wc' -> return wc'

mkCacheGeneration :: Int -> IO CacheGeneration
mkCacheGeneration sz =
    do w <- newIORef []
       parent <- if sz <= 2
                 then return Nothing
                 else liftM Just $ mkCacheGeneration $ sz `div` 2
       return $ CacheGeneration { cg_max_size = sz,
                                  cg_workers = w,
                                  cg_parent = parent }

initWorkerCache :: Worker -> IO ()
initWorkerCache start =
    do cg <- mkCacheGeneration 64
       writeIORef globalWorkerCache $ Just $ WorkerCache { wc_cache = cg,
                                                           wc_start = start }

killCacheGeneration :: CacheGeneration -> IO ()
killCacheGeneration cg =
    do w <- readIORef $ cg_workers cg
       mapM_ (killWorker . snd) w
       case cg_parent cg of
         Nothing -> return ()
         Just x -> killCacheGeneration x

destroyWorkerCache :: IO ()
destroyWorkerCache =
    do wc <- workerCache
       killCacheGeneration $ wc_cache wc
       killWorker $ wc_start wc
       return ()

{- getBestWorkerForHist state: the best history found so far, and
   something which gets the relevant worker and updates the cache. -}
type GBState = (History, IO Worker)

getBestWorkerForHist :: CacheGeneration -> History -> GBState -> IO GBState
getBestWorkerForHist cg hist state =
    let compareStates :: GBState -> GBState -> GBState
        compareStates a@(hist1, _) b@(hist2, _) =
            if not $ hist1 `historyPrefixOf` hist
            then b
            else if hist1 `historyPrefixOf` hist2
                 then b
                 else a
    in
    do {- Search parent caches first.  It doesn't actually matter which
          order we use, since we're going to search the whole tree anyway. -}
       state' <- case cg_parent cg of
                   Nothing -> return state
                   Just parent -> getBestWorkerForHist parent hist state
       local_workers <- readIORef $ cg_workers cg
       let entries :: [(History, Worker)] -> [(History, Worker)] -> [GBState]
           entries [] _ = []
           entries ((x@(xhist,worker)):xs) o =
               (xhist, let nl = o ++ xs
                       in do writeIORef (cg_workers cg) nl
                             registerWorker xhist worker
                             return worker):(entries xs (o ++ [x]))
       return $ foldr compareStates state' $ entries local_workers []

getBestWorker :: History -> IO GBState
getBestWorker hist =
    do cg <- liftM wc_cache workerCache
       getBestWorkerForHist cg hist (emptyHistory, liftM wc_start workerCache)

getWorker :: History -> IO (Bool, Worker)
getWorker hist =

    {- This is a bit skanky.  The problem is that hist might contain
       some thunks which will themselves perform worker cache
       operations, and if we were to force them at exactly the wrong
       time then it's possible that they could modify the cache while
       we have a reference to the old cache state, which would
       potentially cause us to touch dead workers.  We avoid the issue
       completely by just forcing hist before doing anything -}
    force hist $

    do (best_hist, best_worker_io) <- getBestWorker hist
       best_worker <- best_worker_io
       new_worker <- takeSnapshot best_worker
       let new_worker' = case new_worker of
                           Nothing ->
                               error $ "cannot snapshot " ++ (show best_hist)
                           Just new_worker'' -> new_worker''
       cost <- fixupWorkerForHist new_worker' best_hist hist
       return (cost > 10, {- 10 is pretty arbitrary, but seemed to work well
                             in some preliminary testing. -}
               new_worker')


registerWorker :: History -> Worker -> IO ()
registerWorker hist worker =

    {- Preserve sanity by requiring that the worker cache not contain
       any unforced thunks, which might themselves call back into the
       worker cache. -}
    force hist $ force worker $

    let registerWorkerCG :: Maybe CacheGeneration -> (History, Worker) -> IO ()
        registerWorkerCG Nothing (_, w) = killWorker w
        registerWorkerCG (Just cg) what =
            do oldWorkers <- readIORef $ cg_workers cg
               let newWorkers = what:oldWorkers
                   nr_items_this_level = length newWorkers
               if nr_items_this_level > cg_max_size cg
                then assert (nr_items_this_level == cg_max_size cg + 1) $
                     let (newNewWorkers, [dead]) = splitAt (cg_max_size cg) newWorkers
                     in do r <- randomIO
                           if r
                            then registerWorkerCG (cg_parent cg) dead
                            else killWorker $ snd dead
                           writeIORef (cg_workers cg) newNewWorkers
                else writeIORef (cg_workers cg) newWorkers
    in
    do cg <- liftM wc_cache $ workerCache
       registerWorkerCG (Just cg) (hist, worker)


traceCmd :: HistoryEntry -> History -> (Worker -> IO a) -> (History, a)
traceCmd he start w =
    let newHist = appendHistory start he
    in unsafePerformIO $ do (register, worker) <- getWorker start
                            r <- w worker
                            if register
                             then registerWorker newHist worker
                             else killWorker worker
                            return (newHist, r)

run :: History -> Topped EpochNr -> History
run start cntr = appendHistory start $ HistoryRun cntr

trace :: History -> Topped EpochNr -> (History, [TraceRecord])
trace start cntr =
    dt ("trace " ++ (show start) ++ " " ++ (show cntr)) $
    traceCmd (HistoryRun cntr) start $ \worker -> traceWorker worker cntr

traceThread :: History -> ThreadId -> (History, [TraceRecord])
traceThread start thr =
    dt ("traceThread " ++ (show start) ++ " " ++ (show thr)) $
    traceCmd (HistoryRunThread thr) start $ \worker -> traceThreadWorker worker thr

traceAddress :: History -> Word64 -> (History, [TraceRecord])
traceAddress start addr =
    traceCmd (HistoryRun Infinity) start $ \worker -> traceAddressWorker worker addr

runMemory :: History -> ThreadId -> Integer -> (History, [TraceRecord])
runMemory start tid cntr =
    dt ("runMemory " ++ (show start) ++ " " ++ (show tid) ++ " " ++ (show cntr)) $
    traceCmd (HistoryRunMemory tid cntr) start $
            \worker -> runMemoryWorker worker tid cntr

queryCmd :: History -> (Worker -> IO a) -> a
queryCmd hist w =
    unsafePerformIO $ do (register, worker) <- getWorker hist
                         res <- w worker
                         if register
                          then registerWorker hist worker
                          else killWorker worker
                         return res

threadState :: History -> [(ThreadId, ThreadState)]
threadState hist = dt ("replayState " ++ (show hist)) $ queryCmd hist threadStateWorker

replayState :: History -> ReplayState
replayState hist = dt ("replayState " ++ (show hist)) $ queryCmd hist replayStateWorker

controlTrace :: History -> Topped Integer -> [Expression]
controlTrace hist cntr =
    dt ("controlTrace " ++ (show hist) ++ " " ++ (show cntr)) $ snd $ traceCmd (HistoryRun Infinity) hist $ \worker -> controlTraceWorker worker cntr

fetchMemory :: History -> Word64 -> Word64 -> Maybe [Word8]
fetchMemory hist addr size =
    queryCmd hist $ \worker -> fetchMemoryWorker worker addr size

vgIntermediate :: History -> Word64 -> Maybe String
vgIntermediate hist addr =
    queryCmd hist $ \worker -> vgIntermediateWorker worker addr

nextThread :: History -> ThreadId
nextThread hist =
    dt ("nextThread " ++ (show hist)) $ queryCmd hist nextThreadWorker
