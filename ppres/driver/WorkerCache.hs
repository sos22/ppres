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

import System.IO.Unsafe

import Types
import Worker
import History


globalWorkerCache :: IORef (Maybe WorkerCache)
{-# NOINLINE globalWorkerCache #-}
globalWorkerCache =
    unsafePerformIO $ newIORef Nothing

sanityCheckWorkerCache :: WorkerCache -> IO ()
sanityCheckWorkerCache wc =
    mapM_ (\(_,w) -> do r <- readIORef $ worker_alive w
                        if not r
                           then error "found a dead worker in the cache"
                           else return ()) $ wc_workers wc

workerCache :: IO WorkerCache
workerCache =
    do wc <- readIORef globalWorkerCache
       case wc of
         Nothing -> error "worker cache not ready"
         Just wc' -> sanityCheckWorkerCache wc' >> return wc'

setWorkerCache :: WorkerCache -> IO ()
setWorkerCache = writeIORef globalWorkerCache . Just

initWorkerCache :: Worker -> IO ()
initWorkerCache start =
    writeIORef globalWorkerCache $ Just $ WorkerCache { wc_workers = [],
                                                        wc_start = start }

destroyWorkerCache :: IO ()
destroyWorkerCache =
    do wc <- workerCache
       mapM_ (killWorker . snd) $ wc_workers wc
       killWorker $ wc_start wc
       return ()

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

    do (best_hist, best_worker) <- findBestWorker
       new_worker <- takeSnapshot best_worker
       let new_worker' = case new_worker of
                           Nothing ->
                               error $ "cannot snapshot " ++ (show best_hist)
                           Just new_worker'' -> new_worker''
       fixupWorkerForHist new_worker' best_hist hist
       return (best_hist /= hist, new_worker')
    where findBestWorker :: IO (History, Worker)
          findBestWorker =
              do wc <- workerCache
                 return $ foldr compareWorkers
                            (emptyHistory, wc_start wc)
                            (wc_workers wc)
              where
                {- Compare two entries in the worker list, and return
                   whichever one is better suited to the target
                   history -}
                compareWorkers a@(hist1, _) b@(hist2, _) =
                    if not $ hist1 `historyPrefixOf` hist
                    then b
                    else if hist1 `historyPrefixOf` hist2
                         then b
                         else a


registerWorker :: History -> Worker -> IO ()
registerWorker hist worker =

    {- Preserve sanity by requiring that the worker cache not contain
       any unforced thunks, which might themselves call back into the
       worker cache. -}
    force hist $ force worker $

    do wc <- workerCache
       let (new_workers, dead_workers) =
               splitAt 100 ((hist, worker):(wc_workers wc))
       setWorkerCache $ wc { wc_workers = new_workers}
       mapM_ (killWorker . snd) dead_workers


traceCmd :: HistoryEntry -> History -> (Worker -> IO a) -> (History, a)
traceCmd he start w =
    let newHist = appendHistory start he
    in unsafePerformIO $ do (_, worker) <- getWorker start
                            r <- w worker
                            registerWorker newHist worker
                            return (newHist, r)

run :: History -> Topped EpochNr -> History
run start cntr = appendHistory start $ HistoryRun cntr


trace :: History -> Topped EpochNr -> (History, [TraceRecord])
trace start cntr =
    traceCmd (HistoryRun cntr) start $ \worker -> traceWorker worker cntr

traceThread :: History -> ThreadId -> (History, [TraceRecord])
traceThread start thr =
    traceCmd (HistoryRunThread thr) start $ \worker -> traceThreadWorker worker thr

traceAddress :: History -> Word64 -> (History, [TraceRecord])
traceAddress start addr =
    traceCmd (HistoryRun Infinity) start $ \worker -> traceAddressWorker worker addr

runMemory :: History -> ThreadId -> Integer -> (History, [TraceRecord])
runMemory start tid cntr =
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
threadState hist = queryCmd hist threadStateWorker

replayState :: History -> ReplayState
replayState hist = queryCmd hist replayStateWorker

controlTrace :: History -> Topped Integer -> [Expression]
controlTrace hist cntr =
    snd $ traceCmd (HistoryRun Infinity) hist $ \worker -> controlTraceWorker worker cntr

fetchMemory :: History -> Word64 -> Word64 -> Maybe [Word8]
fetchMemory hist addr size =
    queryCmd hist $ \worker -> fetchMemoryWorker worker addr size

vgIntermediate :: History -> Word64 -> Maybe String
vgIntermediate hist addr =
    queryCmd hist $ \worker -> vgIntermediateWorker worker addr

nextThread :: History -> ThreadId
nextThread hist =
    queryCmd hist nextThreadWorker
