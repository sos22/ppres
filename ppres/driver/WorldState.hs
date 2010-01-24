module WorldState(initialWorldState, doAssignment, lookupVariable,
                  lookupSnapshot, doRename, run, trace, traceThread,
                  traceAddress, runMemory, exitWorld) where

import System.Exit
import Foreign.C.Types
import Control.Monad.State
import Data.Word

import Socket
import Types
import UIValue
import Worker
import History

initialWorldState :: CInt -> IO WorldState
initialWorldState fd =
    do f <- fdToSocket fd
       let root_snap = Worker f
       return $ WorldState { ws_bindings = [("start", UIValueSnapshot emptyHistory)],
                             ws_workers = [],
                             ws_starting_worker = root_snap }

lookupVariable :: VariableName -> WorldMonad (Maybe UIValue)
lookupVariable name =
    do s <- get
       return $ lookup name $ ws_bindings s

lookupSnapshot :: VariableName -> WorldMonad (Maybe History)
lookupSnapshot name =
    do s <- lookupVariable name
       case s of
         Just (UIValueSnapshot s') -> return $ Just s'
         _ -> do liftIO $ putStrLn $ name ++ " is not a snapshot"
                 return Nothing

doAssignment :: VariableName -> UIValue -> WorldMonad ()
doAssignment name val =
    do v <- lookupVariable name
       case v of
         Nothing -> return ()
         Just oldVal -> uiv_destruct oldVal
       modify $ \ws -> ws { ws_bindings = (name, val):
                            [b | b <- (ws_bindings ws), fst b /= name]}

{- We impose, in effect, a linear type system on the client language,
   so you can rename stuff but not duplicate it. -}
doRename :: VariableName -> VariableName -> WorldMonad ()
doRename dest src =
    do s <- lookupVariable src
       d <- lookupVariable dest
       case s of
         Nothing -> liftIO $ putStrLn $ "can't find " ++ src
         Just s' ->
             do case d of
                  Nothing -> return ()
                  Just d' -> uiv_destruct d'
                modify $ \ws -> ws { ws_bindings = (dest,s'):
                                    [(n, v) | (n, v) <- ws_bindings ws,
                                              n /= src && n/= dest] }

getWorker :: History -> WorldMonad Worker
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
    where findBestWorker :: WorldMonad (History, Worker)
          findBestWorker =
              do ws <- get
                 return $ foldr compareWorkers
                            (emptyHistory, ws_starting_worker ws)
                            (ws_workers ws)
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


registerWorker :: History -> Worker -> WorldMonad ()
registerWorker hist worker =
    do ws <- get
       let (new_workers, dead_workers) =
               splitAt 100 ((hist, worker):(ws_workers ws))
       put $ ws { ws_workers = new_workers}
       mapM_ (killWorker . snd) dead_workers

cmd :: HistoryEntry -> History -> (Worker -> WorldMonad a) -> WorldMonad (Maybe History)
cmd he start w =
    let newHist = appendHistory start he
    in do worker <- getWorker start
          w worker
          registerWorker newHist worker
          return $ Just newHist

run :: History -> Integer -> WorldMonad (Maybe History)
run start cntr =
    cmd (HistoryRun cntr) start $ \worker -> runWorker worker cntr

trace :: History -> Integer -> WorldMonad (Maybe History)
trace start cntr =
    cmd (HistoryRun cntr) start $ \worker -> traceWorker worker cntr

traceThread :: History -> ThreadId -> WorldMonad (Maybe History)
traceThread start thr =
    cmd (HistoryRunThread thr) start $ \worker -> traceThreadWorker worker thr

traceAddress :: History -> Word64 -> WorldMonad (Maybe History)
traceAddress start addr =
    cmd (HistoryRun $ -1) start $ \worker -> traceAddressWorker worker addr

runMemory :: History -> ThreadId -> Integer -> WorldMonad (Maybe History)
runMemory start tid cntr =
    cmd (HistoryRunMemory tid cntr) start $
            \worker -> runMemoryWorker worker tid cntr

exitWorld :: WorldMonad ()
exitWorld =
    do workers <- liftM ws_workers get
       mapM_ (killWorker . snd) workers
       start <- liftM ws_starting_worker get
       killWorker start
       liftIO $ exitWith ExitSuccess
