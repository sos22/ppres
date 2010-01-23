module WorldState(initialWorldState) where

import Data.IORef
import Foreign.C.Types

import Socket
import Types
import Snapshot

initialWorldState :: CInt -> IO WorldState
initialWorldState fd =
    do f <- fdToSocket fd
       next_id <- newIORef 1
       let root_snap = Snapshot f 0
       worker <- activateSnapshot root_snap
       case worker of
         Nothing -> error "cannot activate root snapshot"
         Just w ->
           return $ WorldState { ws_worker = w,
                                 ws_snapshots = [],
                                 ws_root_snapshot = root_snap,
                                 ws_next_snap_id = next_id }