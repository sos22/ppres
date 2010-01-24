{- This module is intended to hide all the grubbiness of the interface
   to the C world, and provides a nice functional API to it.  The
   functional API is expressed entirely in terms of Histories, and we
   are responsible for mapping them into Workers as and when
   necessary. -}
module WorkerCache(initWorkerCache, destroyWorkerCache, run,
                   trace, traceThread, traceAddress, runMemory,
                   threadState) where

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
       r <- fixupWorkerForHist new_worker' best_hist hist
       case r of
         False -> error $ "failed to move worker from history " ++ (show best_hist) ++ " to " ++ (show hist)
         True -> return ()
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


cmd :: HistoryEntry -> History -> (Worker -> IO a) -> Maybe History
cmd he start w =
    let newHist = appendHistory start he
    in unsafePerformIO $ do worker <- getWorker start
                            w worker
                            registerWorker newHist worker
                            return $ Just newHist

run :: History -> Integer -> Maybe History
run start cntr =
    cmd (HistoryRun cntr) start $ \worker -> runWorker worker cntr

trace :: History -> Integer -> Maybe History
trace start cntr =
    cmd (HistoryRun cntr) start $ \worker -> traceWorker worker cntr

traceThread :: History -> ThreadId -> Maybe History
traceThread start thr =
    cmd (HistoryRunThread thr) start $ \worker -> traceThreadWorker worker thr

traceAddress :: History -> Word64 -> Maybe History
traceAddress start addr =
    cmd (HistoryRun $ -1) start $ \worker -> traceAddressWorker worker addr

runMemory :: History -> ThreadId -> Integer -> Maybe History
runMemory start tid cntr =
    cmd (HistoryRunMemory tid cntr) start $
            \worker -> runMemoryWorker worker tid cntr

threadState :: History -> Maybe [String]
threadState hist =
    unsafePerformIO $ do worker <- getWorker hist
                         res <- threadStateWorker worker
                         killWorker worker
                         return res
