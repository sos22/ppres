module WorldState(initialWorldState, doAssignment, lookupVariable,
                  exitWorld, WorldState(..)) where

import System.Exit
import Foreign.C.Types
import Control.Monad.State
import Data.IORef

import Socket
import Types
import History
import WorkerCache
import UIValue

data WorldState = WorldState { ws_bindings :: [(VariableName, UIValue)] }


initialWorldState :: CInt -> IO WorldState
initialWorldState fd =
    do f <- fdToSocket fd
       a <- newIORef True
       let root_snap = Worker f a
       initWorkerCache root_snap
       return $ WorldState { ws_bindings = [("start", UIValueSnapshot emptyHistory)] }

lookupVariable :: WorldState -> VariableName -> UIValue
lookupVariable ws name =
    case lookup name $ ws_bindings ws of
      Nothing -> UIValueError $ name ++ " not found"
      Just s' -> s'

doAssignment :: WorldState -> VariableName -> UIValue -> WorldState
doAssignment ws name val =
    ws { ws_bindings = (name, val):
         [b | b <- (ws_bindings ws), fst b /= name]}

exitWorld :: IO ()
exitWorld = do destroyWorkerCache
               exitWith ExitSuccess
