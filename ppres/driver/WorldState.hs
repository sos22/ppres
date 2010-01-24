module WorldState(initialWorldState, doAssignment, lookupVariable,
                  exitWorld) where

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

lookupVariable :: WorldState -> VariableName -> UIValue
lookupVariable ws name =
    case lookup name $ ws_bindings ws of
      Nothing -> UIValueError $ name ++ " not found"
      Just s' -> s'

doAssignment :: VariableName -> UIValue -> WorldMonad ()
doAssignment name val =
    modify $ \ws -> ws { ws_bindings = (name, val):
                         [b | b <- (ws_bindings ws), fst b /= name]}

exitWorld :: IO ()
exitWorld = do destroyWorkerCache
               exitWith ExitSuccess
