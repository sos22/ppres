module Worker(killWorker, traceWorker, traceToEventWorker,
              takeSnapshot, runWorker, threadStateWorker,
              replayStateWorker, controlTraceWorker, fetchMemoryWorker,
              vgIntermediateWorker, nextThreadWorker, setThreadWorker,
              getRegistersWorker, setRegisterWorker, allocateMemoryWorker,
              setMemoryWorker, setMemoryProtectionWorker, setTscWorker)
    where

import Data.Word
import Network.Socket
import Control.Monad.State
import Data.IORef
import System.IO.Unsafe
import Data.List

import Types
import Socket

instance Forcable x => Forcable (IORef x) where
    force ref res =
        unsafePerformIO $ do x <- readIORef ref
                             return $ force x res

instance Forcable Worker where
    force (Worker fd alive) = force fd . force alive 

sendWorkerCommand :: Worker -> ControlPacket -> IO ResponsePacket
sendWorkerCommand worker cp =
    do a <- readIORef $ worker_alive worker
       if not a
        then error $ "send command to dead worker on fd " ++ (show $ worker_fd worker)
        else sendSocketCommand (worker_fd worker) cp

fromAN :: Topped AccessNr -> [Word64]
fromAN Infinity = [-1]
fromAN (Finite (AccessNr acc)) = [fromInteger acc]

snapshotPacket :: ControlPacket
snapshotPacket = ControlPacket 0x1234 []

killPacket :: ControlPacket
killPacket = ControlPacket 0x1235 []

runPacket :: Topped AccessNr -> ControlPacket
runPacket x = ControlPacket 0x1236 $ fromAN x

tracePacket :: Topped AccessNr -> ControlPacket
tracePacket x = ControlPacket 0x1237 $ fromAN x

threadStatePacket :: ControlPacket
threadStatePacket = ControlPacket 0x123b []

replayStatePacket :: ControlPacket
replayStatePacket = ControlPacket 0x123c []

controlTracePacket :: Topped AccessNr -> ControlPacket
controlTracePacket to = ControlPacket 0x123d $ fromAN to

fetchMemoryPacket :: Word64 -> Word64 -> ControlPacket
fetchMemoryPacket addr size = ControlPacket 0x123e [addr, size]

vgIntermediatePacket :: Word64 -> ControlPacket
vgIntermediatePacket addr = ControlPacket 0x123f [addr]

nextThreadPacket :: ControlPacket
nextThreadPacket = ControlPacket 0x1240 []

setThreadPacket :: ThreadId -> ControlPacket
setThreadPacket (ThreadId tid) = ControlPacket 0x1241 [fromInteger tid]

getRegistersPacket :: ControlPacket
getRegistersPacket = ControlPacket 0x1242 []

traceToEventPacket :: Topped AccessNr -> ControlPacket
traceToEventPacket x = ControlPacket 0x1243 $ fromAN x

setRegisterPacket :: ThreadId -> RegisterName -> Word64 -> ControlPacket
setRegisterPacket (ThreadId tid) reg val = ControlPacket 0x1244 [fromInteger tid, unparseRegister reg, val]

allocateMemoryPacket :: Word64 -> Word64 -> Word64 -> ControlPacket
allocateMemoryPacket addr size prot = ControlPacket 0x1245 [addr, size, prot]

setMemoryPacket :: Word64 -> Word64 -> ControlPacket
setMemoryPacket addr size = ControlPacket 0x1246 [addr, size]

setMemoryProtectionPacket :: Word64 -> Word64 -> Word64 -> ControlPacket
setMemoryProtectionPacket addr size prot = ControlPacket 0x1247 [addr, size, prot]

setTscPacket :: ThreadId -> Word64 -> ControlPacket
setTscPacket (ThreadId tid) tsc = ControlPacket 0x1248 [fromInteger tid, tsc]

trivCommand :: Worker -> ControlPacket -> IO Bool
trivCommand worker cmd =
    do (ResponsePacket s _) <- sendWorkerCommand worker cmd
       return s

killWorker :: Worker -> IO ()
killWorker worker =
    do s <- trivCommand worker killPacket
       if s
          then do sClose $ worker_fd worker
                  writeIORef (worker_alive worker) False
          else error "can't kill worker?"

runWorker :: Worker -> Topped AccessNr -> IO Bool
runWorker worker = trivCommand worker . runPacket

ancillaryDataToTrace :: [ResponseData] -> [TraceRecord]
ancillaryDataToTrace [] = []
ancillaryDataToTrace ((ResponseDataString _):rs) = ancillaryDataToTrace rs
ancillaryDataToTrace ((ResponseDataBytes _):rs) = ancillaryDataToTrace rs
ancillaryDataToTrace ((ResponseDataAncillary code (loc':tid':other_args)):rs) =
    let loc = AccessNr $ fromIntegral loc'
        tid = ThreadId $ fromIntegral tid'
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
              17 -> (TraceSignal { trc_rip = other_args!!0,
                                   trc_signr = fromIntegral $ other_args!!1,
                                   trc_err = other_args!!2,
                                   trc_va = other_args!!3 }, rs)
              _ -> error $ "bad trace ancillary code " ++ (show code)
    in (TraceRecord { trc_trc = entry, trc_tid = tid, trc_loc = loc }):(ancillaryDataToTrace rest)
ancillaryDataToTrace x = error $ "bad trace ancillary data " ++ (show x)
         

traceCmd :: Worker -> ControlPacket -> IO [TraceRecord]
traceCmd worker pkt =
    do (ResponsePacket _ args) <- sendWorkerCommand worker pkt
       return $ ancillaryDataToTrace args

traceWorker :: Worker -> ThreadId -> Topped AccessNr -> IO [TraceRecord]
traceWorker worker tid cntr = setThreadWorker worker tid >> traceCmd worker (tracePacket cntr)

traceToEventWorker :: Worker -> ThreadId -> Topped AccessNr -> IO [TraceRecord]
traceToEventWorker worker tid limit = do setThreadWorker worker tid
                                         traceCmd worker $ traceToEventPacket limit

takeSnapshot :: Worker -> IO (Maybe Worker)
takeSnapshot worker =
    do (ResponsePacket s _) <- sendWorkerCommand worker snapshotPacket
       if s
        then do newFd <- recvSocket (worker_fd worker)
                newAlive <- newIORef True
                return $ Just $ Worker {worker_fd = newFd, worker_alive = newAlive }
        else return Nothing

threadStateWorker :: Worker -> IO [(ThreadId, ThreadState)]
threadStateWorker worker =
    let parseItem :: ConsumerMonad ResponseData (ThreadId, ThreadState)
        parseItem = do (ResponseDataAncillary 13 [tid, is_dead, is_crashed, last_access, last_rip]) <- consume
                       return (ThreadId $ fromIntegral tid,
                               ThreadState {ts_dead = is_dead /= 0,
                                            ts_crashed = is_crashed /= 0,
                                            ts_last_run = AccessNr $ fromIntegral last_access,
                                            ts_last_rip = last_rip})
    in
      do (ResponsePacket s params) <- sendWorkerCommand worker threadStatePacket
         return $ if s
                  then evalConsumer params (consumeMany parseItem)
                  else error "error getting thread state"

 
parseReplayState :: [ResponseData] -> ReplayState
parseReplayState [ResponseDataAncillary 10 [access_nr]] = ReplayStateOkay $ AccessNr $ fromIntegral access_nr
parseReplayState (ResponseDataAncillary 11 [x, tid, access_nr]:(ResponseDataString s):items) =
    ReplayStateFailed s (ThreadId $ fromIntegral tid) (AccessNr $ fromIntegral access_nr) $
                      case x of
                        0 -> case items of
                               [] -> FailureReasonControl
                               _ -> error $ "unexpected extra data in a failure control response " ++ (show items)
                        1 -> uncurry FailureReasonData $  evalConsumer items $ pairM parseExpression parseExpression
                        3 -> case items of
                               [ResponseDataAncillary 18 [wantedTid]] ->
                                   FailureReasonWrongThread (ThreadId $ fromIntegral wantedTid)
                               _ -> error $ "can't parse data for wrong thread failure " ++ (show items)
                        _ -> error $ "unexpected failure class " ++ (show x)
parseReplayState [ResponseDataAncillary 14 [access_nr]] = ReplayStateFinished $ AccessNr $ fromIntegral access_nr
parseReplayState x = error $ "bad replay state " ++ (show x)

replayStateWorker :: Worker -> IO ReplayState
replayStateWorker worker =
    do (ResponsePacket _ params) <- sendWorkerCommand worker replayStatePacket
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

pairM :: Monad m => m b -> m c -> m (b, c)
pairM a b =
    do a' <- a
       b' <- b
       return $ (a', b')

evalConsumer :: [a] -> ConsumerMonad a b -> b
evalConsumer items monad =
    case runConsumer monad items of
      (x, []) -> x
      _ -> error "Failed to consume all items"

regNames :: [(RegisterName, Word64)]
regNames = [(REG_RAX, 0), (REG_RCX, 1), (REG_RDX, 2), (REG_RBX, 3), (REG_RSP, 4),
            (REG_RBP, 5), (REG_RSI, 6), (REG_RDI, 7), (REG_R8, 8), (REG_R9, 9),
            (REG_R10, 10), (REG_R11, 11), (REG_R12, 12), (REG_R13, 13),
            (REG_R14, 14), (REG_R15, 15), (REG_CC_OP, 16), (REG_CC_DEP1, 17),
            (REG_CC_DEP2, 18), (REG_CC_NDEP, 19), (REG_DFLAG, 20),
            (REG_RIP, 21), (REG_IDFLAG, 22), (REG_FS_ZERO, 23),
            (REG_SSE_ROUND, 24)]

unparseRegister :: RegisterName -> Word64
unparseRegister rname =
    maybe (error $ "bad register name" ++ (show rname) ++ "?") id $ lookup rname regNames

parseRegister :: Word64 -> RegisterName
parseRegister idx =
    maybe (error $ "bad register encoding " ++ (show idx)) fst $
    find ((==) idx . snd) regNames

consumeRegisterBinding :: ConsumerMonad ResponseData (RegisterName, Word64)
consumeRegisterBinding =
    do (ResponseDataAncillary 16 [name, val]) <- consume
       return (parseRegister name, val)

isBinop :: Word64 -> Bool
isBinop x = x >= 5 && x <= 20

parseBinop :: Word64 -> Binop
parseBinop 5 = BinopCombine
parseBinop 6 = BinopSub
parseBinop 7 = BinopAdd
parseBinop 8 = BinopMull
parseBinop 9 = BinopMullHi
parseBinop 10 = BinopMullS
parseBinop 11 = BinopShrl
parseBinop 12 = BinopShl
parseBinop 13 = BinopShra
parseBinop 14 = BinopAnd
parseBinop 15 = BinopOr
parseBinop 16 = BinopXor
parseBinop 17 = BinopLe
parseBinop 18 = BinopBe
parseBinop 19 = BinopEq
parseBinop 20 = BinopB
parseBinop x = error $ "unknown binop " ++ (show x)

parseExpression :: ConsumerMonad ResponseData Expression
parseExpression =
    do d <- consume
       let (ResponseDataAncillary 12 params) = d
       case params of
         [0, val] -> return $ ExpressionConst val
         [1, reg, val] -> return $ ExpressionRegister (parseRegister reg) val
         [2, sz, acc, tid] ->
             do ptr <- parseExpression
                val <- parseExpression
                return $ ExpressionLoad (ThreadId $ fromIntegral tid) (fromIntegral sz) (fromIntegral acc) ptr val
         [3, acc, tid] -> do val <- parseExpression
                             return $ ExpressionStore (ThreadId $ fromIntegral tid) (fromIntegral acc) val
         [4, val] -> return $ ExpressionImported val
         [r] | isBinop r -> do a1 <- parseExpression
                               a2 <- parseExpression
                               return $ ExpressionBinop (parseBinop r) a1 a2
         [21] -> do e <- parseExpression
                    return $ ExpressionNot e

         _ -> error $ "failed to parse an expression " ++ (show d)

parseExpressions :: [ResponseData] -> [Expression]
parseExpressions items =
    evalConsumer items $ consumeMany parseExpression

controlTraceWorker :: Worker -> ThreadId -> Topped AccessNr -> IO [Expression]
controlTraceWorker worker tid cntr =
    do setThreadWorker worker tid
       (ResponsePacket _ params) <- sendWorkerCommand worker $ controlTracePacket cntr
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

nextThreadWorker :: Worker -> IO ThreadId
nextThreadWorker worker =
    do (ResponsePacket True [ResponseDataAncillary 15 [tid]]) <- sendWorkerCommand worker nextThreadPacket
       return $ ThreadId $ fromIntegral tid

setThreadWorker :: Worker -> ThreadId -> IO ()
setThreadWorker worker tid =
    do sendWorkerCommand worker $ setThreadPacket tid
       return ()

getRegistersWorker :: Worker -> IO RegisterFile
getRegistersWorker worker =
    do (ResponsePacket True params) <- sendWorkerCommand worker getRegistersPacket
       return $ RegisterFile $ evalConsumer params $ consumeMany consumeRegisterBinding

setRegisterWorker :: Worker -> ThreadId -> RegisterName -> Word64 -> IO Bool
setRegisterWorker worker tid reg val =
    trivCommand worker $ setRegisterPacket tid reg val

allocateMemoryWorker :: Worker -> Word64 -> Word64 -> Word64 -> IO Bool
allocateMemoryWorker worker addr size prot =
    trivCommand worker $ allocateMemoryPacket addr size prot

setMemoryWorker :: Worker -> Word64 -> [Word8] -> IO Bool
setMemoryWorker worker addr bytes =
    let cp = setMemoryPacket addr $ fromIntegral $ length bytes
    in do a <- readIORef $ worker_alive worker
          if not a
           then error "set memory in dead worker"
           else do (ResponsePacket s _) <- sendSocketCommandTrailer (worker_fd worker) cp bytes
                   return s

setMemoryProtectionWorker :: Worker -> Word64 -> Word64 -> Word64 -> IO ()
setMemoryProtectionWorker worker addr size prot =
    do trivCommand worker $ setMemoryProtectionPacket addr size prot
       return ()

setTscWorker :: Worker -> ThreadId -> Word64 -> IO Bool
setTscWorker worker tid tsc =
    trivCommand worker $ setTscPacket tid tsc
