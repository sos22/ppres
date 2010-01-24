module Worker(withWorker,
              killWorker, traceThreadWorker, traceWorker, runMemoryWorker,
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

runWorker :: Worker -> Integer -> WorldMonad ()
runWorker worker cntr =
    do ack <- sendWorkerCommand worker 0x1236 [fromInteger cntr]
       if ack /= 0
          then liftIO $ putStrLn "error running worker"
          else return ()

traceWorker :: Worker -> Integer -> WorldMonad ()
traceWorker worker cntr =
    do ack <- sendWorkerCommand worker 0x1237 [fromInteger cntr]
       if ack /= 0
          then liftIO $ putStrLn "error running worker"
          else return ()

traceThreadWorker :: Worker -> ThreadId -> WorldMonad ()
traceThreadWorker worker tid =
    do ack <- sendWorkerCommand worker 0x1239 [fromInteger tid]
       if ack /= 0
          then liftIO $ putStrLn "error running worker"
          else return ()

traceAddressWorker :: Worker -> Word64 -> WorldMonad ()
traceAddressWorker worker addr =
    do ack <- sendWorkerCommand worker 0x123a [addr]
       if ack /= 0
          then liftIO $ putStrLn "error running worker"
          else return ()

runMemoryWorker :: Worker -> ThreadId -> Integer -> WorldMonad ()
runMemoryWorker worker tid cntr =
    do ack <- sendWorkerCommand worker 0x1238 [fromInteger $ tid, fromInteger $ cntr]
       if ack /= 0
          then liftIO $ putStrLn "error running worker"
          else return ()

withWorker :: (Worker -> WorldMonad ()) -> WorldMonad ()
withWorker f = get >>= (f . ws_worker)

takeSnapshot :: Worker -> WorldMonad (Maybe Worker)
takeSnapshot worker =
    do ack <- sendWorkerCommand worker 0x1234 []
       if ack < 0
          then return Nothing
          else do newFd <- recvSocket (worker_fd worker)
                  return $ Just $ Worker {worker_fd = newFd }

