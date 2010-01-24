module WorldState(initialWorldState, doAssignment, lookupVariable,
                  lookupSnapshot, exitWorld) where

import System.Exit
import Foreign.C.Types
import Control.Monad.State

import Socket
import Types
import History
import WorkerCache

initialWorldState :: CInt -> IO WorldState
initialWorldState fd =
    do f <- fdToSocket fd
       let root_snap = Worker f
       initWorkerCache root_snap
       return $ WorldState { ws_bindings = [("start", UIValueSnapshot emptyHistory)] }

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
    modify $ \ws -> ws { ws_bindings = (name, val):
                         [b | b <- (ws_bindings ws), fst b /= name]}

exitWorld :: WorldMonad ()
exitWorld =
    liftIO $ do destroyWorkerCache
                exitWith ExitSuccess
