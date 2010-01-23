module Snapshot(killSnapshot, activateSnapshot) where

import Data.Word
import Data.Int
import Network.Socket
import Socket

import Types

sendSnapshotCommand :: Snapshot -> Word32 -> [Word64] -> IO Int32
sendSnapshotCommand snapshot command args =
    sendSocketCommand (snapshot_fd snapshot) command args

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

