module Types where

import Network.Socket
import Control.Monad.State

type ThreadId = Integer
type VariableName = String

data Worker = Worker { worker_fd :: Socket }

data UIValue = UIValueNull
             | UIValueSnapshot Worker

data WorldState = WorldState { ws_worker :: Worker,
                               ws_bindings :: [(VariableName, UIValue)] }


type WorldMonad a = StateT WorldState IO a
