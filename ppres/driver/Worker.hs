module Worker(killWorker, traceThreadWorker, traceWorker, runMemoryWorker,
              takeSnapshot, runWorker, traceAddressWorker, threadStateWorker)
    where

import Data.Word
import Network.Socket
import Control.Monad.State

import Types
import Socket

sendWorkerCommand :: Worker -> ControlPacket -> IO ResponsePacket
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

trivCommand :: Worker -> ControlPacket -> IO Bool
trivCommand worker cmd =
    do (ResponsePacket s _) <- sendWorkerCommand worker cmd
       return s

killWorker :: Worker -> IO Bool
killWorker worker =
    do s <- trivCommand worker killPacket
       if s
          then liftIO $ sClose $ worker_fd worker
          else return ()
       return s

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
    do (ResponsePacket s _) <-
           sendWorkerCommand worker (ControlPacket 0x1234 [])
       if s
        then do newFd <- recvSocket (worker_fd worker)
                return $ Just $ Worker {worker_fd = newFd }
        else return Nothing

threadStateWorker :: Worker -> IO (Maybe [String])
threadStateWorker worker =
    do (ResponsePacket s params) <-
           sendWorkerCommand worker (ControlPacket 0x123b [])
       return $
              if s
              then Just [x | (ResponseDataString x) <- params]
              else Nothing
 