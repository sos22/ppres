module Worker(killWorker, traceThreadWorker, traceWorker, runMemoryWorker,
              takeSnapshot, runWorker, traceAddressWorker, threadStateWorker)
    where

import Data.Word
import Data.Int
import Network.Socket
import Control.Monad.State

import Types
import Socket

sendWorkerCommand :: Worker -> ControlPacket -> IO Int32
sendWorkerCommand worker cp =
    sendSocketCommand (worker_fd worker) cp

killPacket :: ControlPacket
killPacket = ControlPacket 0x1235 []

runPacket :: Integer -> ControlPacket
runPacket cntr = ControlPacket 0x1236 [fromInteger cntr]

tracePacket :: Integer -> ControlPacket
tracePacket cntr = ControlPacket 0x1237 [fromInteger cntr]

runMemoryPacket :: ThreadId -> Integer -> ControlPacket
runMemoryPacket tid cntr = ControlPacket 0x1238 [fromIntegral tid, fromInteger cntr]

traceThreadPacket :: ThreadId -> ControlPacket
traceThreadPacket tid = ControlPacket 0x1239 [fromInteger tid]

traceAddressPacket :: Word64 -> ControlPacket
traceAddressPacket addr = ControlPacket 0x123a [addr]

killWorker :: Worker -> IO Bool
killWorker worker =
    do ack <- sendWorkerCommand worker killPacket
       if ack == 0
          then do liftIO $ sClose $ worker_fd worker
                  return True
          else return False

trivCommand :: Worker -> ControlPacket -> IO Bool
trivCommand worker cmd =
    do ack <- sendWorkerCommand worker cmd
       return $ ack == 0

runWorker :: Worker -> Integer -> IO Bool
runWorker worker = trivCommand worker . runPacket

traceWorker :: Worker -> Integer -> IO Bool
traceWorker worker = trivCommand worker . tracePacket

traceThreadWorker :: Worker -> ThreadId -> IO Bool
traceThreadWorker worker = trivCommand worker . traceThreadPacket

traceAddressWorker :: Worker -> Word64 -> IO Bool
traceAddressWorker worker = trivCommand worker . traceAddressPacket

runMemoryWorker :: Worker -> ThreadId -> Integer -> IO Bool
runMemoryWorker worker tid = trivCommand worker . runMemoryPacket tid

takeSnapshot :: Worker -> IO (Maybe Worker)
takeSnapshot worker =
    do ack <- sendWorkerCommand worker (ControlPacket 0x1234 [])
       if ack < 0
          then return Nothing
          else do newFd <- recvSocket (worker_fd worker)
                  return $ Just $ Worker {worker_fd = newFd }


threadStateWorker :: Worker -> IO (Maybe String)
threadStateWorker worker =
    do len <- sendWorkerCommand worker (ControlPacket 0x123b [])
       if len < 0
          then return Nothing
          else liftM Just $ recvStringBytes (worker_fd worker) len
