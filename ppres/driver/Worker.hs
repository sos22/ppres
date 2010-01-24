module Worker(killWorker, traceThreadWorker, traceWorker, runMemoryWorker,
              takeSnapshot, runWorker, traceAddressWorker
             ) where

import Data.Word
import Data.Int
import Network.Socket
import Control.Monad.State

import Types
import Socket

sendWorkerCommand :: Worker -> Word32 -> [Word64] -> WorldMonad Int32
sendWorkerCommand worker command args =
    sendSocketCommand (worker_fd worker) command args

killWorker :: Worker -> WorldMonad Bool
killWorker worker =
    do ack <- sendWorkerCommand worker 0x1235 []
       if ack == 0
          then do liftIO $ sClose $ worker_fd worker
                  return True
          else return False

runWorker :: Worker -> Integer -> WorldMonad Bool
runWorker worker cntr =
    do ack <- sendWorkerCommand worker 0x1236 [fromInteger cntr]
       return $ ack == 0

traceWorker :: Worker -> Integer -> WorldMonad Bool
traceWorker worker cntr =
    do ack <- sendWorkerCommand worker 0x1237 [fromInteger cntr]
       return $ ack == 0

traceThreadWorker :: Worker -> ThreadId -> WorldMonad Bool
traceThreadWorker worker tid =
    do ack <- sendWorkerCommand worker 0x1239 [fromInteger tid]
       return $ ack == 0

traceAddressWorker :: Worker -> Word64 -> WorldMonad Bool
traceAddressWorker worker addr =
    do ack <- sendWorkerCommand worker 0x123a [addr]
       return $ ack == 0

runMemoryWorker :: Worker -> ThreadId -> Integer -> WorldMonad Bool
runMemoryWorker worker tid cntr =
    do ack <- sendWorkerCommand worker 0x1238 [fromInteger $ tid, fromInteger $ cntr]
       return $ ack == 0

takeSnapshot :: Worker -> WorldMonad (Maybe Worker)
takeSnapshot worker =
    do ack <- sendWorkerCommand worker 0x1234 []
       if ack < 0
          then return Nothing
          else do newFd <- recvSocket (worker_fd worker)
                  return $ Just $ Worker {worker_fd = newFd }

