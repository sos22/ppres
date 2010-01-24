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

ancillaryDataToTrace :: [ResponseData] -> [TraceRecord]
ancillaryDataToTrace [] = []
ancillaryDataToTrace ((ResponseDataString _):rs) = ancillaryDataToTrace rs
ancillaryDataToTrace ((ResponseDataAncillary code args):rs) =
    let (loc', other_args) = splitAt 3 args
        loc = TraceLocation { trc_record = toInteger $ loc'!!0,
                              trc_access = toInteger $ loc'!!1,
                              trc_thread = fromIntegral $ loc'!!2 }
        (entry, rest) =
            case code of
              1 -> (TraceFootstep { trc_foot_rip = fromIntegral $ other_args!!0,
                                    trc_foot_rdx = fromIntegral $ other_args!!1,
                                    trc_foot_rcx = fromIntegral $ other_args!!2,
                                    trc_foot_rax = fromIntegral $ other_args!!3 },
                    rs)
              2 -> (TraceSyscall { trc_sys_nr = fromIntegral $ other_args!!0 },
                    rs)
              3 -> (TraceRdtsc, rs)
              4 -> (TraceLoad { trc_load_val = fromIntegral $ other_args!!0,
                                trc_load_size = fromIntegral $ other_args!!1,
                                trc_load_ptr = fromIntegral $ other_args!!2,
                                trc_load_in_monitor = other_args!!3 /= 0 }, rs)
              5 -> (TraceStore { trc_store_val = fromIntegral $ other_args!!0,
                                 trc_store_size = fromIntegral $ other_args!!1,
                                 trc_store_ptr = fromIntegral $ other_args!!2,
                                 trc_store_in_monitor = other_args!!3 /= 0 }, rs)
              6 -> (case head rs of
                      ResponseDataString s -> TraceCalling s
                      _ -> error "mangled trace", tail rs)
              7 -> (case head rs of
                      ResponseDataString s -> TraceCalled s
                      _ -> error "mangled trace", tail rs)
              8 -> (TraceEnterMonitor, rs)
              9 -> (TraceExitMonitor, rs)
              _ -> error $ "bad trace ancillary code " ++ (show code)
    in (TraceRecord { trc_trc = entry, trc_loc = loc }):(ancillaryDataToTrace rest)
         
    
traceWorker :: Worker -> Integer -> IO [TraceRecord]
traceWorker worker cntr =
    do (ResponsePacket s args) <- sendWorkerCommand worker $ tracePacket cntr
       if s then return $ ancillaryDataToTrace args
          else return []

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
 