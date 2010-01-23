module Snapshot(killSnapshot, getSnapshot, activateSnapshot) where

import Data.Word
import Data.Int
import Network.Socket
import Socket

import Types

sendSnapshotCommand :: Snapshot -> Word32 -> [Word64] -> IO Int32
sendSnapshotCommand snapshot command args =
    sendSocketCommand (snapshot_fd snapshot) command args

getSnapshot :: WorldState -> SnapshotId -> Maybe Snapshot
getSnapshot ws sid =
    worker (ws_snapshots ws)
    where worker [] = if sid == (snapshot_id $ ws_root_snapshot ws)
                      then Just $ ws_root_snapshot ws
                      else Nothing
          worker (s:ss) = if snapshot_id s == sid then Just s
                          else worker ss

activateSnapshot :: Snapshot -> IO (Maybe Worker)
activateSnapshot ss =
    do ack <- sendSnapshotCommand ss 0xabce []
       if ack /= 0
        then return Nothing
        else do fd <- recvSocket (snapshot_fd ss)
                return $ Just $ Worker { worker_fd = fd }

killSnapshot :: Snapshot -> IO Bool
killSnapshot worker =
    do ack <- sendSnapshotCommand worker 0xabcd []
       if ack == 0
          then do sClose $ snapshot_fd worker
                  return True
          else return False

