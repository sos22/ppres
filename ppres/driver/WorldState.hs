module WorldState(initialWorldState) where

import Data.IORef
import Foreign.C.Types

import Socket
import Types

initialWorldState :: CInt -> IO WorldState
initialWorldState fd =
    do f <- fdToSocket fd
       next_id <- newIORef 1
       return $ WorldState { ws_worker = Nothing,
                             ws_snapshots = [],
                             ws_root_snapshot = Snapshot f 0,
                             ws_next_snap_id = next_id }