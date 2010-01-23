module Types where

import Network.Socket

type SnapshotId = String
type ThreadId = Integer

data Worker = Worker { worker_fd :: Socket }
data Snapshot = Snapshot { snapshot_fd :: Socket,
                           snapshot_id :: SnapshotId }
data WorldState = WorldState { ws_worker :: Worker,
                               ws_snapshots :: [Snapshot],
                               ws_root_snapshot :: Snapshot }

