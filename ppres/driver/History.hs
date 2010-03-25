module History(
               emptyHistory, 
               truncateHistory, History,

               {- Single-stop operations on snapshots. -}
               runThread, setRegister, allocateMemory, setMemory, setMemoryProtection,
               setTsc,

               {- Queries on histories -}
               threadAtAccess, threadState, replayState, fetchMemory, vgIntermediate,
               nextThread, getRegisters, getRipAtAccess,

               {- Trace operations -}
               traceTo, controlTraceTo, traceToEvent,

               {- Other stuff -}
               initWorkerCache, destroyWorkerCache               
               ) where

import Control.Monad.Error
import Data.Word
import Data.IORef
import System.IO.Unsafe
import Network.Socket
import Data.List

import Types
import Util
import Socket
import Logfile

--import qualified Debug.Trace
dt :: String -> a -> a
dt = const id


data HistoryEntry = HistoryRun !ThreadId !(Topped AccessNr)
                  | HistorySetRegister !ThreadId !RegisterName !Word64
                  | HistoryAllocMemory !Word64 !Word64 !Word64
                  | HistorySetMemory !Word64 [Word8]
                  | HistorySetMemoryProtection !Word64 !Word64 !Word64
                  | HistorySetTsc !ThreadId !Word64
                  | HistoryAdvanceLog !LogfilePtr
                    deriving (Eq, Show, Read)

{- We cache, in the history record, the last epoch in the history and
   the number of entries in the history.  This means we can do a quick
   out in historyPrefixOf in many useful cases. -}
{- The logfile ptr is for the *start* of the log, not the current
   position. -}
data History = History { hs_start_lp :: LogfilePtr,
                         hs_contents :: DList HistoryEntry } deriving (Show, Eq, Read)

last_coord :: [HistoryEntry] -> Topped AccessNr
last_coord he = worker $ reverse he
                where worker [] = Finite $ AccessNr 0
                      worker ((HistoryRun _ x):_) = x
                      worker (_:x) = worker x

history_logfile_ptr :: History -> LogfilePtr
history_logfile_ptr (History st hes) =
    foldr (\x y -> case x of
                     HistoryAdvanceLog z -> z
                     _ -> y) st $ reverse $ dlToList hes

mkHistory :: LogfilePtr -> [HistoryEntry] -> History
mkHistory startlp h = History startlp (listToDl h)

{- Estimate of cost of going from a to b. -}
replayCost :: AccessNr-> AccessNr -> Integer
replayCost a b =
    toInteger $ b - a

doHistoryEntry :: Worker -> HistoryEntry -> IO Integer
doHistoryEntry w (HistoryRun tid cntr) =
    do setThreadWorker w tid
       rs <- replayStateWorker w
       case rs of
         ReplayStateOkay e ->
             do r <- runWorker w cntr
                if not r
                   then putStrLn $ "failed to replay history entry run " ++ (show tid) ++ " " ++ (show cntr) ++ " in " ++ (show w)
                   else return ()
                rs' <- replayStateWorker w
                case rs' of
                  ReplayStateFinished e' -> return $ replayCost e e'
                  ReplayStateFailed _ _ e' _ ->
                      return $ replayCost e e'
                  ReplayStateOkay e' -> return $ replayCost e e'
         ReplayStateFinished _ -> return 1
         ReplayStateFailed _ _ _ _ -> return 1
doHistoryEntry w (HistorySetRegister tid reg val) =
    do setRegisterWorker w tid reg val
       return 1
doHistoryEntry w (HistoryAllocMemory addr size prot) =
    do allocateMemoryWorker w addr size prot
       return 1
doHistoryEntry w (HistorySetMemory addr bytes) =
    do setMemoryWorker w addr bytes
       return $ (toInteger $ length bytes) `div` 4096
doHistoryEntry w (HistorySetMemoryProtection addr size prot) =
    do setMemoryProtectionWorker w addr size prot
       return 1
doHistoryEntry w (HistorySetTsc tid tsc) =
    do setTscWorker w tid tsc
       return 1
doHistoryEntry _ (HistoryAdvanceLog _) = return 0

stripSharedPrefix' :: [HistoryEntry] -> [HistoryEntry] -> [HistoryEntry] -> ([HistoryEntry], [HistoryEntry], [HistoryEntry])
stripSharedPrefix' x a [] = (reverse x, a, [])
stripSharedPrefix' x [] b = (reverse x, [], b)
stripSharedPrefix' rprefix aas@(a:as) bbs@(b:bs) =
    if a == b then stripSharedPrefix' (a:rprefix) as bs
    else case (a, b) of
           (HistoryRun atid an, HistoryRun btid bn) | atid == btid ->
             if an < bn
             then stripSharedPrefix' (a:rprefix) as bbs
             else stripSharedPrefix' (b:rprefix) aas bs
           _ -> (reverse rprefix, (a:as), (b:bs))

stripSharedPrefix :: History -> History -> ([HistoryEntry], [HistoryEntry])
stripSharedPrefix (History _ aa) (History _ bb) =
    case stripSharedPrefix' (error "stripSharedPrefix") (dlToList aa) (dlToList bb) of
      (_, a, b) -> (a, b)

emptyHistory :: LogfilePtr -> History
emptyHistory lp = mkHistory lp []

appendHistory :: History -> HistoryEntry -> Either String History
appendHistory (History startlp dlh) he =
    let h = dlToList dlh
        revh = reverse h
        (hl:hrest) = revh
    in case h of
         [] -> Right $ mkHistory startlp [he]
         _ ->
             do h' <-
                    case (hl, he) of
                      (HistoryRun xtid x, HistoryRun ytid y)
                          | x == y -> Right h {- didn't advance -> no-op -}
                          | y < x -> Left "appendHistory tried to go backwards in time!"
                          | xtid == ytid -> Right $ reverse $ he:hrest
                          | otherwise -> Right $ reverse $ he:revh
                      _ -> Right $ reverse $ he:revh
                let res = History startlp $ listToDl h'
                return res

{- Truncate a history so that it only runs to a particular epoch number -}
truncateHistory :: History -> Topped AccessNr -> Either String History
truncateHistory (History startlp hs) cntr =
    let worker [HistoryRun tid Infinity] = Right [HistoryRun tid cntr]
        worker ((HistoryRun tid c):hs') =
            if c < cntr then liftM ((:) $ HistoryRun tid c) $ worker hs'
            else Right [HistoryRun tid cntr]
        worker _ = Left $ "truncate bad history: " ++ (show hs) ++ " to " ++ (show cntr)
    in liftM (mkHistory startlp) (worker $ dlToList hs)

threadAtAccess :: History -> AccessNr -> Either String ThreadId
threadAtAccess (History _ items) acc =
    foldr (\(HistoryRun tid acc') rest ->
               if (Finite acc) < acc'
               then Right tid
               else rest) (Left "ran out of history") $ dlToList items

instance Forcable HistoryEntry where
    force (HistorySetMemory _ r) = force r
    force x = seq x

instance Forcable History where
    force (History l h) = force l . force h

traceTo' :: Worker -> (Worker -> ThreadId -> Topped AccessNr -> IO [a]) -> [HistoryEntry] -> IO [a]
traceTo' _ _ [] = return []
traceTo' work tracer ((HistoryRun tid cntr):rest) =
    do h <- tracer work tid cntr
       rest' <- traceTo' work tracer rest
       return $ h ++ rest'
traceTo' work tracer ((HistorySetRegister tid reg val):rest) =
    do setRegisterWorker work tid reg val
       traceTo' work tracer rest
traceTo' work tracer ((HistoryAllocMemory addr size prot):rest) =
    do allocateMemoryWorker work addr size prot
       traceTo' work tracer rest
traceTo' work tracer ((HistorySetMemory addr bytes):rest) =
    do setMemoryWorker work addr bytes
       traceTo' work tracer rest
traceTo' work tracer ((HistorySetMemoryProtection addr size prot):rest) =
    do setMemoryProtectionWorker work addr size prot
       traceTo' work tracer rest
traceTo' work tracer ((HistorySetTsc tid tsc):rest) =
    do setTscWorker work tid tsc
       traceTo' work tracer rest
traceTo' worker tracer ((HistoryAdvanceLog _):rest) =
    traceTo' worker tracer rest

{- Take a worker and a history representing its current state and run
   it forwards to some other history, logging control expressions as
   we go. -}
{- This arguably belongs in Worker.hs, but that would mean exposing
   the internals of the History type. -}
controlTraceToWorker :: Worker -> History -> History -> IO (Either String [Expression])
controlTraceToWorker work start end =
    let worker = traceTo' work controlTraceWorker
    in
    case stripSharedPrefix start end of
      ([], todo) -> liftM Right $ worker todo
      _ -> return $ Left $ (show start) ++ " is not a prefix of " ++ (show end)

{- Ditto: should be in Worker.hs, but don't want to expose the innards
   of History. -}
traceToWorker :: Worker -> History -> History -> IO (Either String [TraceRecord])
traceToWorker worker start end =
    let work = traceTo' worker traceWorker
    in case stripSharedPrefix start end of
         ([], todo) -> liftM Right $ work todo
         _ -> return $ Left $ shows start $ " is not a prefix of " ++ (show end)

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

getHistoryPacket :: ControlPacket
getHistoryPacket = ControlPacket 0x1249 []

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

validateHistoryWorker :: Worker -> [HistoryEntry] -> IO Bool
validateHistoryWorker worker desired_hist =
    let validateHistory [] [] = True
        validateHistory ((ResponseDataAncillary 19 [0x1236, tid, acc]):o) o's@((HistoryRun tid' acc'):o')
            | (ThreadId $ toInteger tid) == tid' =
                case (Finite $ AccessNr $ toInteger acc) `compare` acc' of
                  LT -> validateHistory o o's
                  EQ -> validateHistory o o'
                  GT -> dt ("history validation failed because worker was at " ++ (show acc) ++ " and we only wanted " ++ (show acc') ++ ", rest " ++ (show o')) False
        validateHistory ((ResponseDataAncillary 19 [0x1244, tid, reg, val]):o)
                        ((HistorySetRegister tid' reg' val'):o')
            | (ThreadId $ toInteger tid) == tid' && (parseRegister reg) == reg' && val == val' = validateHistory o o'
        validateHistory ((ResponseDataAncillary 19 [0x1245, addr, size, prot]):o)
                        ((HistoryAllocMemory addr' size' prot'):o')
            | addr == addr' && size == size' && prot == prot' = validateHistory o o'
        validateHistory ((ResponseDataAncillary 19 [0x1246, addr, size]):o)
                        ((HistorySetMemory addr' bytes):o')
            | addr == addr' && size == (fromIntegral $ length bytes) = validateHistory o o'
        validateHistory ((ResponseDataAncillary 19 [0x1247, addr, size, prot]):o)
                        ((HistorySetMemoryProtection addr' size' prot'):o')
            | addr == addr' && size == size' && prot == prot' = validateHistory o o'
        validateHistory ((ResponseDataAncillary 19 [0x1248, tid, tsc]):o)
                        ((HistorySetTsc tid' tsc'):o')
            | (ThreadId $ toInteger tid) == tid' && tsc == tsc' = validateHistory o o'
        validateHistory o ((HistoryAdvanceLog _):o') = validateHistory o o'
        validateHistory o o' = dt ("history validation failed: " ++ (show o) ++ " vs " ++ (show o')) False
    in do (ResponsePacket _ params) <- sendWorkerCommand worker getHistoryPacket
          return $ validateHistory params desired_hist

{- The worker cache.  The cache is structured as an n-ary tree.  Each
   edge is labelled with a history entry.  Each node is labelled with
   a sequence of history entries, and sometimes also with a worker.
   The edges leaving any given node are distinct and non-overlapping.
   For every worker, concatenating all of the history entries on the
   path from the root to that worker gives the worker's current state.
   If an edge is labelled HistoryRun, the counter is always zero, and
   is ignored.

   We also thread a cyclic double-linked list through every node in
   the tree, which is used for LRU expiry.

   The root entry is special, because it can never be expired.  It is
   used to mark the end of the linked lists.  Its parent is itself.
-}
data WorkerCacheEntry = WorkerCacheEntry {
      wce_id :: Integer,
      wce_worker :: IORef (Maybe Worker),
      wce_history_entries :: IORef [HistoryEntry],
      wce_children :: IORef [(HistoryEntry, WorkerCacheEntry)],
      wce_parent :: WorkerCacheEntry,
      wce_is_root :: Bool,

      wce_next_lru :: IORef WorkerCacheEntry,
      wce_prev_lru :: IORef WorkerCacheEntry
 }

instance Show WorkerCacheEntry where
    show x = "<WCE " ++ (show $ wce_id x) ++ ">"

data WorkerCache = WorkerCache { wc_cache_root :: WorkerCacheEntry,
                                 wc_logfile :: Logfile,
                                 wc_remaining_ids :: IORef [Integer],
                                 wc_nr_workers :: IORef Int
                               }

sanityCheckWorkerCache :: WorkerCache -> IO Bool
sanityCheckWorkerCache wc =
    sanityCheckWorkerCacheTree [] (wc_cache_root wc)
    where sanityCheckWorkerCacheTree prefix wce =
              do e <- readIORef $ wce_history_entries wce
                 let local_hist = prefix ++ e
                 worker <- readIORef $ wce_worker wce
                 v <- case worker of
                   Nothing -> return True
                   Just w -> do r <- validateHistoryWorker w local_hist
                                when (not r) $
                                 putStrLn $ "worker cache sanity check failed at " ++ (show worker) ++ ": wanted history " ++ (show local_hist)
                                return r
                 childs <- readIORef $ wce_children wce
                 children_sane <- mapM (\(hist_entry, child) ->
                                            let child_prefix =
                                                    case hist_entry of
                                                      HistoryRun _ _ -> local_hist
                                                      _ -> local_hist ++ [hist_entry]
                                            in sanityCheckWorkerCacheTree child_prefix child) childs
                 return $ and $ v:children_sane

checkWorkerCache :: WorkerCache -> IO ()
checkWorkerCache wc =
    do r <- sanityCheckWorkerCache wc
       assert r $ return ()

{- Pull a WCE to the front of the LRU list -}
touchWorkerCacheEntry :: WorkerCache -> WorkerCacheEntry -> IO ()
touchWorkerCacheEntry wc wce =
    if wce_is_root wce
    then return ()
    else do {- Remove from old place -}
            prev <- readIORef $ wce_prev_lru wce
            next <- readIORef $ wce_next_lru wce
            writeIORef (wce_next_lru prev) next
            writeIORef (wce_prev_lru next) prev

            {- Insert in new place -}
            addWceToList wc wce

addWceToList :: WorkerCache -> WorkerCacheEntry -> IO ()
addWceToList wc wce =
    let newPrev = wc_cache_root wc
    in do newNext <- readIORef $ wce_next_lru newPrev
          writeIORef (wce_next_lru wce) newNext
          writeIORef (wce_prev_lru wce) newPrev
          writeIORef (wce_next_lru newPrev) wce
          writeIORef (wce_prev_lru newNext) wce

assert :: Bool -> a -> a
assert True = id
assert False = error "assertion failure"

killWorkerTree :: WorkerCache -> WorkerCacheEntry -> IO ()
killWorkerTree wc wce =
    do w <- readIORef $ wce_worker wce
       case w of
         Nothing -> return ()
         Just w' -> do modifyIORef (wc_nr_workers wc) $ \x -> x - 1
                       killWorker w'
       writeIORef (wce_worker wce) Nothing
       children <- readIORef $ wce_children wce
       mapM_ (killWorkerTree wc . snd) children

removeWorkerCacheEntry :: WorkerCache -> WorkerCacheEntry -> IO ()
removeWorkerCacheEntry wc wce =
    assert (not $ wce_is_root wce) $
       do {- First, remove from the linked list. -}
          prev <- readIORef $ wce_prev_lru wce
          next <- readIORef $ wce_next_lru wce
          writeIORef (wce_next_lru prev) next
          writeIORef (wce_prev_lru next) prev

          {- Next, remove from the parent -}
          modifyIORef (wce_children $ wce_parent wce) $ filter (\(_,x) -> wce_id x /= wce_id wce)

          {- Finally, kill all the workers which we just unhooked -}
          killWorkerTree wc wce

          checkWorkerCache wc

foldrM :: Monad m => (a -> m b -> m b) -> m b -> [a] -> m b
foldrM _ base [] = base
foldrM iter base (a:as) =
    iter a (foldrM iter base as)

fixupWorkerCache :: WorkerCache -> IO ()
fixupWorkerCache wc =
    do nrWorkers <- readIORef $ wc_nr_workers wc
       if nrWorkers >= cacheSize
          then do lastWce <- readIORef $ wce_prev_lru $ wc_cache_root wc
                  dt ("Trim cache: remove " ++ (show lastWce) ++ ", have " ++ (show nrWorkers) ++ ", want " ++ (show cacheSize)) $ removeWorkerCacheEntry wc lastWce
                  fixupWorkerCache wc
          else checkWorkerCache wc

registerWorker :: History -> Worker -> IO ()
registerWorker hist worker =
    force hist $
    force worker $
    dt ("register worker " ++ (show worker) ++ " for " ++ (show hist)) $
    do wc <- workerCache
       checkWorkerCache wc
       v <- validateHistoryWorker worker (dlToList $ hs_contents hist)
       assert v $ addWorkerCacheEntry wc (wc_cache_root wc) (dlToList $ hs_contents hist) worker
       modifyIORef (wc_nr_workers wc) ((+) 1)
       fixupWorkerCache wc
       checkWorkerCache wc

addWorkerCacheEntry :: WorkerCache -> WorkerCacheEntry -> [HistoryEntry] -> Worker -> IO ()
addWorkerCacheEntry wc cursor hist worker =
    do checkWorkerCache wc
       touchWorkerCacheEntry wc cursor
       cursor_prefix <- readIORef $ wce_history_entries cursor
       case stripSharedPrefix' [] cursor_prefix hist of
         (_, [], []) -> {- We've found the right place to do the insert. -}
                        do cur_worker <- readIORef $ wce_worker cursor
                           case cur_worker of
                             Nothing -> return ()
                             Just x -> 
                                       do killWorker x -- We already had
                                                       -- a worker for
                                                       -- this history.
                                                       -- Replace it.
                                          modifyIORef (wc_nr_workers wc) ((+) (-1))
                           writeIORef (wce_worker cursor) (Just worker)
         (_, [], he@(hist_excess_head:hist_excess)) ->
             {- Try to insert into a child. -}
             do cursor_childs <- readIORef $ wce_children cursor
                foldrM (\(cursor_child_hist, cursor_child) b ->
                            if cursor_child_hist == hist_excess_head
                            then addWorkerCacheEntry wc cursor_child hist_excess worker
                            else case (cursor_child_hist, hist_excess_head) of
                                   (HistoryRun ctid _, HistoryRun htid _) | ctid == htid ->
                                      addWorkerCacheEntry wc cursor_child he worker
                                   _ -> b)
                       (
                        let (newChildEntry, he') = case hist_excess_head of
                                                     HistoryRun tid _ -> (HistoryRun tid 0, he)
                                                     _ -> (hist_excess_head, hist_excess)
                        in
                          do newChildWorker <- newIORef $ Just worker
                             newChildHistoryEntries <- newIORef he'
                             newChildChilds <- newIORef []
                             (newChildId:remainingIds) <- readIORef $ wc_remaining_ids wc
                             writeIORef (wc_remaining_ids wc) remainingIds
                             newChildNext <- newIORef undefined
                             newChildPrev <- newIORef undefined
                             let newChild = WorkerCacheEntry { wce_id = newChildId,
                                                               wce_worker = newChildWorker,
                                                               wce_history_entries = newChildHistoryEntries,
                                                               wce_children = newChildChilds,
                                                               wce_parent = cursor,
                                                               wce_is_root = False,
                                                               wce_next_lru = newChildNext,
                                                               wce_prev_lru = newChildPrev }
                             addWceToList wc newChild
                             writeIORef (wce_children cursor) ((newChildEntry,newChild):cursor_childs))
                       cursor_childs
         (prefix, ce@(cursor_excess_head:cursor_excess), _) ->
             {- We need to split this entry.  Go and do so. -}
             let (childEntry, childHist) = case cursor_excess_head of
                                             HistoryRun tid _ -> (HistoryRun tid 0, ce)
                                             _ -> (cursor_excess_head, cursor_excess)
             in do newChildWorker <- newIORef Nothing
                   newChildHistoryEntries <- newIORef childHist
                   oldChilds <- readIORef $ wce_children cursor
                   newChildChilds <- newIORef oldChilds
                   (newChildId:remainingIds) <- readIORef $ wc_remaining_ids wc
                   writeIORef (wc_remaining_ids wc) remainingIds
                   newChildNext <- newIORef undefined
                   newChildPrev <- newIORef undefined
                   let newChild = WorkerCacheEntry { wce_id = newChildId,
                                                     wce_worker = newChildWorker,
                                                     wce_history_entries = newChildHistoryEntries,
                                                     wce_children = newChildChilds,
                                                     wce_parent = cursor,
                                                     wce_is_root = False,
                                                     wce_next_lru = newChildNext,
                                                     wce_prev_lru = newChildPrev }
                   addWceToList wc newChild
                   writeIORef (wce_children cursor) [(childEntry,newChild)]
                   writeIORef (wce_history_entries cursor) prefix
                   {- Try that again.  This time, we should insert directly into the cursor. -}
                   addWorkerCacheEntry wc cursor hist worker
                                   

getWorkerCacheEntry :: WorkerCache -> WorkerCacheEntry -> [HistoryEntry] -> ([HistoryEntry], Worker) -> IO ([HistoryEntry], Worker)
getWorkerCacheEntry wc cursor hist bestSoFar =
    do checkWorkerCache wc
       touchWorkerCacheEntry wc cursor
       cursor_prefix <- readIORef $ wce_history_entries cursor
       cursor_worker <- readIORef $ wce_worker cursor
       case stripSharedPrefix' undefined cursor_prefix hist of
         (_, [], []) ->
             {- we're done -}
             do cworker <- readIORef $ wce_worker cursor
                return $ case cworker of
                           Nothing -> bestSoFar
                           Just w -> ([], w)             
         (_, [], rh@(rhHead:remainingHist)) ->
               {- Search children -}
               let newBest = case cursor_worker of
                               Nothing -> bestSoFar
                               Just w -> (rh, w)
               in do childs <- readIORef $ wce_children cursor
                     let r =  foldr (\(key, child) rest ->
                                         if key == rhHead
                                         then Just (child, remainingHist)
                                         else case (key, rhHead) of
                                                (HistoryRun ktid _, HistoryRun rtid _) | ktid == rtid
                                                  -> Just (child, rh)
                                                _ -> rest) Nothing childs
                     case r of
                       Nothing -> return newBest
                       Just (child, remainingHist') -> getWorkerCacheEntry wc child remainingHist' newBest
         (_, (_:_), _) -> {- gone too far -}
                          return bestSoFar

cacheSize :: Int
cacheSize = 900

globalWorkerCache :: IORef (Maybe WorkerCache)
{-# NOINLINE globalWorkerCache #-}
globalWorkerCache =
    unsafePerformIO $ newIORef Nothing

workerCache :: IO WorkerCache
workerCache =
    do wc <- readIORef globalWorkerCache
       case wc of
         Nothing -> error "worker cache not ready"
         Just wc' -> return wc'

initWorkerCache :: Logfile -> Worker -> IO ()
initWorkerCache lf start =
    do root_worker <- newIORef $ Just start
       root_entries <- newIORef []
       root_children <- newIORef []
       root_prev <- newIORef undefined
       root_next <- newIORef undefined
       let root = WorkerCacheEntry { wce_id = 0,
                                     wce_worker = root_worker,
                                     wce_history_entries = root_entries,
                                     wce_children = root_children,
                                     wce_parent = root,
                                     wce_is_root = True,
                                     wce_next_lru = root_next,
                                     wce_prev_lru = root_prev }
       writeIORef root_prev root
       writeIORef root_next root
       ids <- newIORef [1..]
       nrWorkers <- newIORef 1
       writeIORef globalWorkerCache $ Just $ WorkerCache { wc_cache_root = root,
                                                           wc_remaining_ids = ids,
                                                           wc_logfile = lf,
                                                           wc_nr_workers = nrWorkers }

destroyWorkerCache :: IO ()
destroyWorkerCache =
    do wc <- workerCache
       killWorkerTree wc $ wc_cache_root wc
       writeIORef globalWorkerCache Nothing

getWorker' :: [HistoryEntry] -> IO Worker
getWorker' target =

    {- This is a bit skanky.  The problem is that hist might contain
       some thunks which will themselves perform worker cache
       operations, and if we were to force them at exactly the wrong
       time then it's possible that they could modify the cache while
       we have a reference to the old cache state, which would
       potentially cause us to touch dead workers.  We avoid the issue
       completely by just forcing hist before doing anything -}
    force target $

    do wc <- workerCache
       checkWorkerCache wc
       (fixup, worker) <- getWorkerCacheEntry wc (wc_cache_root wc) target undefined
       let reallySnapshot x = liftM (maybe (error $ "cannot snapshot " ++ (show x)) id) $ takeSnapshot x
           doFixup currentWorker [] = return currentWorker
           doFixup currentWorker (x:xs) = do doHistoryEntry currentWorker x
                                             doFixup currentWorker xs
       worker' <- dt ("getwce " ++ (show target) ++ " -> " ++ (show fixup) ++ ", " ++ (show worker)) $ reallySnapshot worker
       checkWorkerCache wc
       doFixup worker' fixup
       checkWorkerCache wc
       return worker'

getWorker :: History -> IO Worker
getWorker hist =
    do worker <- getWorker' $ dlToList $ hs_contents hist
       v <- validateHistoryWorker worker (dlToList $ hs_contents hist)
       if not v
          then error $ "worker cache is broken: history " ++ (show hist) ++ " gave worker " ++ (show worker)
          else return worker

queryCmd :: (Worker -> IO a) -> History -> a
queryCmd w hist =
    unsafePerformIO $ do worker <- getWorker hist
                         res <- w worker
                         killWorker worker
                         return res

threadState :: History -> [(ThreadId, ThreadState)]
threadState = queryCmd threadStateWorker

replayState :: History -> ReplayState
replayState = queryCmd replayStateWorker

fetchMemory :: History -> Word64 -> Word64 -> Maybe [Word8]
fetchMemory hist addr size =
    queryCmd (\worker -> fetchMemoryWorker worker addr size) hist

vgIntermediate :: History -> Word64 -> Maybe String
vgIntermediate hist addr =
    queryCmd (\worker -> vgIntermediateWorker worker addr) hist

nextThread :: History -> ThreadId
nextThread = queryCmd nextThreadWorker

controlTraceTo :: History -> History -> Either String [Expression]
controlTraceTo start end =
    queryCmd (\worker -> controlTraceToWorker worker start end) start

traceTo :: History -> History -> Either String [TraceRecord]
traceTo start end = 
    queryCmd (\worker -> traceToWorker worker start end) start

getRegisters :: History -> RegisterFile
getRegisters = queryCmd getRegistersWorker

getRipAtAccess :: History -> AccessNr -> Either String Word64
getRipAtAccess hist whn =
    do hist' <- truncateHistory hist $ Finite $ whn + 1
       getRegister (getRegisters hist') REG_RIP

traceToEvent :: History -> ThreadId -> Topped AccessNr -> Either String ([TraceRecord], History)
traceToEvent start tid limit =
    unsafePerformIO $ do worker <- getWorker start
                         trc <- traceToEventWorker worker tid limit
                         rs <- replayStateWorker worker
                         killWorker worker
                         return $ do h <- runThread start tid $ Finite (rs_access_nr rs)
                                     return (trc, h)

runThread :: History -> ThreadId -> Topped AccessNr -> Either String History
runThread hist tid acc =
    do res <- appendHistory hist $ HistoryRun tid acc
       return $ unsafePerformIO $ do worker <- getWorker hist
                                     setThreadWorker worker tid
                                     r <- runWorker worker acc
                                     if not r
                                        then do putStrLn $ "failed to run worker " ++ (show worker) ++ " from " ++ (show hist) ++ " to " ++ (show tid) ++ ":" ++ (show acc)
                                                killWorker worker
                                        else registerWorker res worker
                                     return res

setRegister :: History -> ThreadId -> RegisterName -> Word64 -> History
setRegister hist tid reg val =
    let res = deError $ appendHistory hist $ HistorySetRegister tid reg val
    in unsafePerformIO $ do worker <- getWorker hist
                            setRegisterWorker worker tid reg val
                            registerWorker res worker
                            return res

allocateMemory :: History -> Word64 -> Word64 -> Word64 -> History
allocateMemory hist addr size prot =
    let res = deError $ appendHistory hist $ HistoryAllocMemory addr size prot
    in unsafePerformIO $ do worker <- getWorker hist
                            allocateMemoryWorker worker addr size prot
                            registerWorker res worker
                            return res

setMemory :: History -> Word64 -> [Word8] -> History
setMemory hist addr contents =
    let res = deError $ appendHistory hist $ HistorySetMemory addr contents
    in unsafePerformIO $ do worker <- getWorker hist
                            setMemoryWorker worker addr contents
                            registerWorker res worker
                            return res

setMemoryProtection :: History -> Word64 -> Word64 -> Word64 -> History
setMemoryProtection hist addr size prot =
    let res = deError $ appendHistory hist $ HistorySetMemoryProtection addr size prot
    in unsafePerformIO $ do worker <- getWorker hist
                            setMemoryProtectionWorker worker addr size prot
                            registerWorker res worker
                            return res

setTsc :: History -> ThreadId -> Word64 -> History
setTsc hist tid tsc =
    let res = deError $ appendHistory hist $ HistorySetTsc tid tsc
    in unsafePerformIO $ do worker <- getWorker hist
                            setTscWorker worker tid tsc
                            registerWorker res worker
                            return res
