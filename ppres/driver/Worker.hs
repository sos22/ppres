module Worker(killWorker, traceThreadWorker, traceWorker, runMemoryWorker,
              takeSnapshot, runWorker, traceAddressWorker, threadStateWorker,
              replayStateWorker, controlTraceWorker, fetchMemoryWorker,
              vgIntermediateWorker)
    where

import Data.Word
import Network.Socket
import Control.Monad.State

import Types
import Socket

sendWorkerCommand :: Worker -> ControlPacket -> IO ResponsePacket
sendWorkerCommand worker cp =
    sendSocketCommand (worker_fd worker) cp

fromTI :: Topped Integer -> Word64
fromTI Infinity = -1
fromTI (Finite x) = fromInteger x

fromRN :: Topped RecordNr -> Word64
fromRN Infinity = -1
fromRN (Finite (RecordNr x)) = fromInteger x

killPacket :: ControlPacket
killPacket = ControlPacket 0x1235 []

runPacket :: (Topped RecordNr) -> ControlPacket
runPacket cntr = ControlPacket 0x1236 [fromRN cntr]

tracePacket :: Topped RecordNr -> ControlPacket
tracePacket cntr = ControlPacket 0x1237 [fromRN cntr]

runMemoryPacket :: ThreadId -> Integer -> ControlPacket
runMemoryPacket tid cntr = ControlPacket 0x1238 [fromIntegral tid, fromInteger cntr]

traceThreadPacket :: ThreadId -> ControlPacket
traceThreadPacket tid = ControlPacket 0x1239 [fromInteger tid]

traceAddressPacket :: Word64 -> ControlPacket
traceAddressPacket addr = ControlPacket 0x123a [addr]

controlTracePacket :: Topped Integer -> ControlPacket
controlTracePacket cntr = ControlPacket 0x123d [fromTI cntr]

fetchMemoryPacket :: Word64 -> Word64 -> ControlPacket
fetchMemoryPacket addr size = ControlPacket 0x123e [addr, size]

vgIntermediatePacket :: Word64 -> ControlPacket
vgIntermediatePacket addr = ControlPacket 0x123f [addr]

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

runWorker :: Worker -> (Topped RecordNr) -> IO Bool
runWorker worker = trivCommand worker . runPacket

ancillaryDataToTrace :: [ResponseData] -> [TraceRecord]
ancillaryDataToTrace [] = []
ancillaryDataToTrace ((ResponseDataString _):rs) = ancillaryDataToTrace rs
ancillaryDataToTrace ((ResponseDataBytes _):rs) = ancillaryDataToTrace rs
ancillaryDataToTrace ((ResponseDataAncillary code args):rs) =
    let (loc', other_args) = splitAt 3 args
        loc = TraceLocation { trc_record = RecordNr $ fromIntegral $ loc'!!0,
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
         

traceCmd :: Worker -> ControlPacket -> IO [TraceRecord]
traceCmd worker pkt =
    do (ResponsePacket _ args) <- sendWorkerCommand worker pkt
       return $ ancillaryDataToTrace args

traceWorker :: Worker -> Topped RecordNr -> IO [TraceRecord]
traceWorker worker cntr = traceCmd worker (tracePacket cntr)

traceThreadWorker :: Worker -> ThreadId -> IO [TraceRecord]
traceThreadWorker worker = traceCmd worker . traceThreadPacket

traceAddressWorker :: Worker -> Word64 -> IO [TraceRecord]
traceAddressWorker worker = traceCmd worker . traceAddressPacket

runMemoryWorker :: Worker -> ThreadId -> Integer -> IO [TraceRecord]
runMemoryWorker worker tid = traceCmd worker . runMemoryPacket tid

takeSnapshot :: Worker -> IO (Maybe Worker)
takeSnapshot worker =
    do (ResponsePacket s _) <-
           sendWorkerCommand worker (ControlPacket 0x1234 [])
       if s
        then do newFd <- recvSocket (worker_fd worker)
                return $ Just $ Worker {worker_fd = newFd }
        else return Nothing

threadStateWorker :: Worker -> IO [(ThreadId, ThreadState)]
threadStateWorker worker =
    let parseItem :: ConsumerMonad ResponseData (ThreadId, ThreadState)
        parseItem = do (ResponseDataAncillary 13 [tid, is_dead, last_record]) <- consume
                       return (fromIntegral $ tid, ThreadState (is_dead /= 0) (RecordNr $ fromIntegral last_record))
    in
      do (ResponsePacket s params) <-
             sendWorkerCommand worker (ControlPacket 0x123b [])
         return $ if s
                  then evalConsumer params (consumeMany parseItem)
                  else error "error getting thread state"

 
parseReplayState :: [ResponseData] -> ReplayState
parseReplayState [ResponseDataAncillary 10 []] = ReplayStateOkay
parseReplayState [ResponseDataAncillary 11 [0, record_nr, tid], ResponseDataString s] =
    ReplayStateFailed s $ FailureReasonControl (RecordNr $ fromIntegral record_nr) (fromIntegral tid)
parseReplayState x = error $ "bad replay state " ++ (show x)

replayStateWorker :: Worker -> IO ReplayState
replayStateWorker worker =
    do (ResponsePacket _ params) <-
           sendWorkerCommand worker (ControlPacket 0x123c [])
       return $ parseReplayState params

data ConsumerMonad a b = ConsumerMonad { runConsumer :: [a] -> (b, [a]) }

instance Monad (ConsumerMonad a) where
    return b = ConsumerMonad $  \r -> (b, r)
    f >>= s =
        ConsumerMonad $ \items ->
            let (f_res, items') = runConsumer f items
            in runConsumer (s f_res) items'

consume :: ConsumerMonad a a
consume = ConsumerMonad $ \(i:r) -> (i,r)

hitEnd :: ConsumerMonad a Bool
hitEnd = ConsumerMonad $ \i -> case i of
                                 [] -> (True, i)
                                 _ -> (False, i)

consumeMany :: ConsumerMonad a b -> ConsumerMonad a [b]
consumeMany what =
    do e <- hitEnd
       if e
          then return []
          else do i <- what
                  rest <- consumeMany what
                  return $ i:rest

evalConsumer :: [a] -> ConsumerMonad a b -> b
evalConsumer items monad =
    case runConsumer monad items of
      (x, []) -> x
      _ -> error "Failed to consume all items"

parseRegister :: Word64 -> RegisterName
parseRegister 0 = REG_RAX
parseRegister 1 = REG_RCX
parseRegister 2 = REG_RDX
parseRegister 3 = REG_RBX
parseRegister 4 = REG_RSP
parseRegister 5 = REG_RBP
parseRegister 6 = REG_RSI
parseRegister 7 = REG_RDI
parseRegister 8 = REG_R8
parseRegister 9 = REG_R9
parseRegister 10 = REG_R10
parseRegister 11 = REG_R11
parseRegister 12 = REG_R12
parseRegister 13 = REG_R13
parseRegister 14 = REG_R14
parseRegister 15 = REG_R15
parseRegister 16 = REG_CC_OP
parseRegister 17 = REG_CC_DEP1
parseRegister 18 = REG_CC_DEP2
parseRegister 19 = REG_CC_NDEP
parseRegister r = error $ "bad register encoding " ++ (show r)

isBinop :: Word64 -> Bool
isBinop x = x >= 4 && x <= 19

parseBinop :: Word64 -> Binop
parseBinop 4 = BinopCombine
parseBinop 5 = BinopSub
parseBinop 6 = BinopAdd
parseBinop 7 = BinopMull
parseBinop 8 = BinopMullHi
parseBinop 9 = BinopMullS
parseBinop 10 = BinopShrl
parseBinop 11 = BinopShl
parseBinop 12 = BinopShra
parseBinop 13 = BinopAnd
parseBinop 14 = BinopOr
parseBinop 15 = BinopXor
parseBinop 16 = BinopLe
parseBinop 17 = BinopBe
parseBinop 18 = BinopEq
parseBinop 19 = BinopB
parseBinop x = error $ "unknown binop " ++ (show x)

parseExpression :: ConsumerMonad ResponseData Expression
parseExpression =
    do d <- consume
       let (ResponseDataAncillary 12 params) = d
       case params of
         [0, val] -> return $ ExpressionConst val
         [1, reg, val] -> return $ ExpressionRegister (parseRegister reg) val
         [2, sz, rec, acc,  thr] ->
             do ptr <- parseExpression
                val <- parseExpression
                return $ ExpressionMem (fromIntegral sz) (TraceLocation (RecordNr $ fromIntegral rec) (fromIntegral acc) (fromIntegral thr)) ptr val
         [3, val] -> return $ ExpressionImported val
         [r] | isBinop r -> do a1 <- parseExpression
                               a2 <- parseExpression
                               return $ ExpressionBinop (parseBinop r) a1 a2
         [20] -> do e <- parseExpression
                    return $ ExpressionNot e

         _ -> error $ "failed to parse an expression " ++ (show d)

parseExpressions :: [ResponseData] -> [Expression]
parseExpressions items =
    evalConsumer items $ consumeMany parseExpression

controlTraceWorker :: Worker -> Topped Integer -> IO [Expression]
controlTraceWorker worker cntr =
    do (ResponsePacket _ params) <-
           sendWorkerCommand worker $ controlTracePacket cntr
       return $ parseExpressions params

fetchMemoryWorker :: Worker -> Word64 -> Word64 -> IO (Maybe [Word8])
fetchMemoryWorker worker addr size =
    do r <- sendWorkerCommand worker $ fetchMemoryPacket addr size
       return $ case r of
                  (ResponsePacket True [ResponseDataBytes s]) -> Just s
                  _ -> Nothing

vgIntermediateWorker :: Worker -> Word64 -> IO (Maybe String)
vgIntermediateWorker worker addr =
    do sendWorkerCommand worker $ vgIntermediatePacket addr
       return Nothing