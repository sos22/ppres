{- This module is intended to hide all the grubbiness of the interface
   to the C world, and provides a nice functional API to it.  The
   functional API is expressed entirely in terms of Histories, and we
   are responsible for mapping them into Workers as and when
   necessary. -}
module WorkerCache(initWorkerCache, destroyWorkerCache, run,
                   trace, traceThread, traceAddress, runMemory,
                   threadState, replayState, controlTrace,
                   fetchMemory, vgIntermediate) where

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

workerCache :: IO WorkerCache
workerCache =
    do wc <- readIORef globalWorkerCache
       case wc of
         Nothing -> error "worker cache not ready"
         Just wc' -> return wc'

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

getWorker :: History -> IO Worker
getWorker hist =
    do (best_hist, best_worker) <- findBestWorker 
       new_worker <- takeSnapshot best_worker
       let new_worker' = case new_worker of
                           Nothing ->
                               error $ "cannot snapshot " ++ (show best_hist)
                           Just new_worker'' -> new_worker''
       fixupWorkerForHist new_worker' best_hist hist
       return new_worker'
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
    do wc <- workerCache
       let (new_workers, dead_workers) =
               splitAt 100 ((hist, worker):(wc_workers wc))
       setWorkerCache $ wc { wc_workers = new_workers}
       mapM_ (killWorker . snd) dead_workers


cmd :: HistoryEntry -> History -> (Worker -> IO a) -> History
cmd he start w =
    let newHist = appendHistory start he
    in unsafePerformIO $ do worker <- getWorker start
                            w worker
                            registerWorker newHist worker
                            return newHist

traceCmd :: HistoryEntry -> History -> (Worker -> IO a) -> (History, a)
traceCmd he start w =
    let newHist = appendHistory start he
    in unsafePerformIO $ do worker <- getWorker start
                            r <- w worker
                            registerWorker newHist worker
                            return (newHist, r)

run :: History -> (Topped Integer) -> History
run start cntr =
    cmd (HistoryRun cntr) start $ \worker -> runWorker worker cntr


trace :: History -> Topped Integer -> (History, [TraceRecord])
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
    unsafePerformIO $ do worker <- getWorker hist
                         res <- w worker
                         killWorker worker
                         return res

threadState :: History -> Maybe [String]
threadState hist = queryCmd hist threadStateWorker

replayState :: History -> ReplayState
replayState hist = queryCmd hist replayStateWorker

controlTrace :: History -> Topped Integer -> [Expression]
controlTrace hist cntr =
    queryCmd hist $ \worker -> controlTraceWorker worker cntr

fetchMemory :: History -> Word64 -> Word64 -> Maybe [Word8]
fetchMemory hist addr size =
    queryCmd hist $ \worker -> fetchMemoryWorker worker addr size

vgIntermediate :: History -> Word64 -> Maybe String
vgIntermediate hist addr =
    queryCmd hist $ \worker -> vgIntermediateWorker worker addr
