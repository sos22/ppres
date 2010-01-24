module Worker(killWorker, traceThreadWorker, traceWorker, runMemoryWorker,
              takeSnapshot, runWorker, traceAddressWorker, threadStateWorker)
    where

import Data.Word
import Data.Int
import Network.Socket
import Control.Monad.State

import Types
import Socket

sendWorkerCommand :: Worker -> Word32 -> [Word64] -> IO Int32
sendWorkerCommand worker command args =
    sendSocketCommand (worker_fd worker) command args

killWorker :: Worker -> IO Bool
killWorker worker =
    do ack <- sendWorkerCommand worker 0x1235 []
       if ack == 0
          then do liftIO $ sClose $ worker_fd worker
                  return True
          else return False

runWorker :: Worker -> Integer -> IO Bool
runWorker worker cntr =
    do ack <- sendWorkerCommand worker 0x1236 [fromInteger cntr]
       return $ ack == 0

traceWorker :: Worker -> Integer -> IO Bool
traceWorker worker cntr =
    do ack <- sendWorkerCommand worker 0x1237 [fromInteger cntr]
       return $ ack == 0

traceThreadWorker :: Worker -> ThreadId -> IO Bool
traceThreadWorker worker tid =
    do ack <- sendWorkerCommand worker 0x1239 [fromInteger tid]
       return $ ack == 0

traceAddressWorker :: Worker -> Word64 -> IO Bool
traceAddressWorker worker addr =
    do ack <- sendWorkerCommand worker 0x123a [addr]
       return $ ack == 0

runMemoryWorker :: Worker -> ThreadId -> Integer -> IO Bool
runMemoryWorker worker tid cntr =
    do ack <- sendWorkerCommand worker 0x1238 [fromInteger $ tid, fromInteger $ cntr]
       return $ ack == 0

takeSnapshot :: Worker -> IO (Maybe Worker)
takeSnapshot worker =
    do ack <- sendWorkerCommand worker 0x1234 []
       if ack < 0
          then return Nothing
          else do newFd <- recvSocket (worker_fd worker)
                  return $ Just $ Worker {worker_fd = newFd }


threadStateWorker :: Worker -> IO (Maybe String)
threadStateWorker worker =
    do len <- sendWorkerCommand worker 0x123b []
       if len < 0
          then return Nothing
          else liftM Just $ recvStringBytes (worker_fd worker) len
