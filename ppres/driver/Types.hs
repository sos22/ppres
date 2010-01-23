module Types where

import Network.Socket

type ThreadId = Integer
type VariableName = String

data Worker = Worker { worker_fd :: Socket }
data Snapshot = Snapshot { snapshot_fd :: Socket }

data UIValue = UIValueNull
             | UIValueSnapshot Snapshot

data WorldState = WorldState { ws_worker :: Worker,
                               ws_bindings :: [(VariableName, UIValue)] }

