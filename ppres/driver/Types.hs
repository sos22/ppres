module Types where

import Network.Socket
import Data.IORef

type SnapshotId = Integer
type ThreadId = Integer

data Worker = Worker { worker_fd :: Socket }
data Snapshot = Snapshot { snapshot_fd :: Socket,
                           snapshot_id :: SnapshotId }
data WorldState = WorldState { ws_worker :: Maybe Worker,
                               ws_snapshots :: [Snapshot],
                               ws_root_snapshot :: Snapshot,
                               ws_next_snap_id :: IORef SnapshotId }

