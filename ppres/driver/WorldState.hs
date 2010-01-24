module WorldState(initialWorldState, doAssignment, lookupVariable,
                  lookupSnapshot, doRename, run, trace, traceThread,
                  traceAddress, runMemory, exitWorld) where

import System.Exit
import Foreign.C.Types
import Control.Monad.State
import Data.Word

import qualified Debug.Trace as DT

import Socket
import Types
import UIValue
import Worker
import History

t :: String -> a -> a
t = DT.trace

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
       new_worker <- t ("Chose " ++ (show best_hist) ++ " as best prefix of " ++ (show hist)) $ takeSnapshot best_worker
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

run :: History -> Integer -> WorldMonad (Maybe History)
run start cntr =
    let newHist = appendHistory start (HistoryRun cntr)
    in
    do worker <- getWorker start
       runWorker worker cntr
       registerWorker newHist worker
       return $ Just newHist

trace :: History -> Integer -> WorldMonad (Maybe History)
trace start cntr =
    let newHist = appendHistory start (HistoryRun cntr)
    in
    do worker <- getWorker start
       traceWorker worker cntr
       registerWorker newHist worker
       return $ Just newHist

traceThread :: History -> ThreadId -> WorldMonad (Maybe History)
traceThread start thr =
    let newHist = appendHistory start (HistoryRunThread thr)
    in
    do worker <- getWorker start
       traceThreadWorker worker thr
       registerWorker newHist worker
       return $ Just newHist

traceAddress :: History -> Word64 -> WorldMonad (Maybe History)
traceAddress start addr =
    let newHist = appendHistory start (HistoryRun $ -1)
    in
    do worker <- getWorker start
       traceAddressWorker worker addr
       registerWorker newHist worker
       return $ Just newHist

runMemory :: History -> ThreadId -> Integer -> WorldMonad (Maybe History)
runMemory start tid cntr =
    let newHist = appendHistory start (HistoryRunMemory tid cntr)
    in
    do worker <- getWorker start
       runMemoryWorker worker tid cntr
       registerWorker newHist worker
       return $ Just newHist

exitWorld :: WorldMonad ()
exitWorld =
    do workers <- liftM ws_workers get
       mapM_ (killWorker . snd) workers
       start <- liftM ws_starting_worker get
       killWorker start
       liftIO $ exitWith ExitSuccess
