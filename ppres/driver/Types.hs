{-# LANGUAGE ExistentialQuantification #-}
module Types where

import Network.Socket

type SnapshotId = String
type ThreadId = Integer
type VariableName = String

data Worker = Worker { worker_fd :: Socket }
data Snapshot = Snapshot { snapshot_fd :: Socket,
                           snapshot_id :: SnapshotId }

data UIValue = forall a. UIValue { uiv_destruct :: IO (),
                                   uiv_show :: String }

data WorldState = WorldState { ws_worker :: Worker,
                               ws_snapshots :: [Snapshot],
                               ws_root_snapshot :: Snapshot,
                               ws_bindings :: [(VariableName, UIValue)] }

