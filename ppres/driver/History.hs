module History(historyPrefixOf, emptyHistory, fixupWorkerForHist,
               appendHistory, truncateHistory, History,
               mkHistory, histLastCoord, controlTraceToWorker,
               traceToWorker, runThread, absHistSuffix, threadAtAccess,
               setRegister, allocateMemory, setMemory, setMemoryProtection,
               setTsc, killWorker, traceWorker, traceToEventWorker,
               takeSnapshot, threadStateWorker, replayStateWorker,
               fetchMemoryWorker, vgIntermediateWorker,
               nextThreadWorker, getRegistersWorker
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

data HistoryEntry = HistoryRun !ThreadId !(Topped AccessNr)
                  | HistorySetRegister !ThreadId !RegisterName !Word64
                  | HistoryAllocMemory !Word64 !Word64 !Word64
                  | HistorySetMemory !Word64 [Word8]
                  | HistorySetMemoryProtection !Word64 !Word64 !Word64
                  | HistorySetTsc !ThreadId !Word64
                    deriving (Eq, Show, Read)

{- We cache, in the history record, the last epoch in the history and
   the number of entries in the history.  This means we can do a quick
   out in historyPrefixOf in many useful cases. -}
data History = History (Topped AccessNr) Int (DList HistoryEntry) deriving (Show, Eq, Read)

runThread :: History -> ThreadId -> Topped AccessNr -> Either String History
runThread hist tid acc =
    appendHistory hist $ HistoryRun tid acc

setRegister :: History -> ThreadId -> RegisterName -> Word64 -> History
setRegister hist tid reg val =
    deError $ appendHistory hist $ HistorySetRegister tid reg val

allocateMemory :: History -> Word64 -> Word64 -> Word64 -> History
allocateMemory hist addr size prot =
    deError $ appendHistory hist $ HistoryAllocMemory addr size prot

setMemory :: History -> Word64 -> [Word8] -> History
setMemory hist addr contents =
    deError $ appendHistory hist $ HistorySetMemory addr contents

setMemoryProtection :: History -> Word64 -> Word64 -> Word64 -> History
setMemoryProtection hist addr size prot =
    deError $ appendHistory hist $ HistorySetMemoryProtection addr size prot

setTsc :: History -> ThreadId -> Word64 -> History
setTsc hist tid tsc =
    deError $ appendHistory hist $ HistorySetTsc tid tsc

histLastCoord :: History -> Topped AccessNr
histLastCoord (History x _ _) = x

last_coord :: [HistoryEntry] -> Topped AccessNr
last_coord he = worker $ reverse he
                where worker [] = Finite $ AccessNr 0
                      worker ((HistoryRun _ x):_) = x
                      worker (_:x) = worker x

{- Either id, for valid histories, or undefined for invalid ones. -}
sanityCheckHistory :: History -> History
sanityCheckHistory hh@(History epoch len h) =
    if len /= dlLength h
    then error $ "History " ++ (show hh) ++ " had bad length (should be " ++ (show $ dlLength h) ++ ")"
    else if last_coord (dlToList h) /= epoch
         then error $ "History " ++ (show hh) ++ " had bad last epoch (should be " ++ (show $ last_coord (dlToList h)) ++ ")"
         else hh

mkHistory :: [HistoryEntry] -> History
mkHistory h = History (last_coord h) (length h) (listToDl h)

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
             do runWorker w cntr
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

stripSharedPrefix :: History -> History -> ([HistoryEntry], [HistoryEntry])
stripSharedPrefix (History _ _ aa) (History _ _ bb) =
    worker (dlToList aa) (dlToList bb)
    where worker a [] = (a, [])
          worker [] b = ([], b)
          worker aas@(a:as) bbs@(b:bs) =
              if a == b then worker as bs
              else case (a, b) of
                     (HistoryRun atid an, HistoryRun btid bn) | atid == btid ->
                         if an < bn
                         then worker as bbs
                         else worker aas bs
                     _ -> ((a:as), (b:bs))

{- a `historyPrefixOf` b -> True iff a is a prefix of b (which includes
   when a and b are equal as a special case) -}
historyPrefixOf :: History -> History -> Bool
historyPrefixOf (History a_last_epoch a_length a) (History b_last_epoch b_length b) =
    if a_length > b_length || a_last_epoch > b_last_epoch
    then False
    else
        let worker aas bbs =
              {-# SCC "historyPrefixOfWorker" #-}
              case (aas, bbs) of
                (Nothing, _) -> True
                (_, Nothing) -> False
                (Just (DListEntry _ as aa), Just (DListEntry _ bs bb)) ->
                    if aa == bb then worker as bs
                    else case (aa, bb) of
                           (HistoryRun atid acntr, HistoryRun btid bcntr) | atid == btid ->
                               if acntr <= bcntr
                               then worker as bbs
                               else False
                           _ -> False
            res = worker (dle_head a) (dle_head b)
        in res

emptyHistory :: History
emptyHistory = mkHistory []

{- fixupWorkerForHist worker current desired -> assume that worker is
   in a state represented by current, and get it into a state
   represented by desired.  current must be a prefix of desired.
   Returns either:

   -- Left an estimate of how much that cost, or

   -- Right intermediate_history if we go over budget.
 -}
fixupWorkerForHist :: Integer -> Worker -> History -> History -> IO (Integer, Maybe History)
fixupWorkerForHist budget w current desired =
    case stripSharedPrefix current desired of
      ([], todo) ->
          worker todo 0 current
          where worker [] cost _ = return (cost, Nothing)
                worker (x:xs) cost so_far =
                    if cost > budget
                    then return $ (cost, Just so_far)
                    else do cost' <- doHistoryEntry w x
                            let (Right r) = appendHistory so_far x
                            worker xs (cost + cost') r
      _ -> error $ (show current) ++ " is not a prefix of " ++ (show desired) ++ " (historyPrefixOf " ++ (show $ historyPrefixOf current desired) ++ ")"

appendHistory :: History -> HistoryEntry -> Either String History
appendHistory (History old_last_epoch old_nr_records dlh) he =
    let h = dlToList dlh
        revh = reverse h
        (hl:hrest) = revh
    in case h of
         [] -> Right $ mkHistory [he]
         _ ->
             do (new_last_epoch, new_nr_records, h') <-
                    case (hl, he) of
                      (HistoryRun xtid x, HistoryRun ytid y)
                          | x == y -> Right (old_last_epoch, old_nr_records, h) {- didn't advance -> no-op -}
                          | y < x -> Left "appendHistory tried to go backwards in time!"
                          | xtid == ytid ->
                              Right (y, old_nr_records, reverse $ he:hrest)
                          | otherwise ->
                              Right (y, old_nr_records + 1, reverse $ he:revh)
                      _ -> Right (old_last_epoch, old_nr_records + 1, reverse $ he:revh)
                let res = History new_last_epoch new_nr_records $ listToDl h'
                return $ sanityCheckHistory res

{- Truncate a history so that it only runs to a particular epoch number -}
truncateHistory :: History -> Topped AccessNr -> Either String History
truncateHistory (History _ _ hs) cntr =
    let worker [HistoryRun tid Infinity] = Right [HistoryRun tid cntr]
        worker ((HistoryRun tid c):hs') =
            if c < cntr then liftM ((:) $ HistoryRun tid c) $ worker hs'
            else Right [HistoryRun tid cntr]
        worker _ = Left $ "truncate bad history: " ++ (show hs) ++ " to " ++ (show cntr)
    in liftM mkHistory (worker $ dlToList hs)

{- Make a new history in which access numbers are all relative to the
   previous access, rather than absolute from the beginning of the
   world. -}
mkRelativeHistory :: AccessNr -> [HistoryEntry] -> [(ThreadId, Integer)]
mkRelativeHistory _ [] = []
mkRelativeHistory (AccessNr base) ((HistoryRun tid (Finite aa@(AccessNr acc))):others) =
    (tid, acc - base):(mkRelativeHistory aa others)
mkRelativeHistory _ [HistoryRun _ Infinity] = error "can't convert infinite history to relative form"
mkRelativeHistory _ _ = error "history is broken: stuff beyond infinity"

relHistToThreadAbs :: [(ThreadId, Integer)] -> [(ThreadId, Integer)] -> [(ThreadId, Integer)]
relHistToThreadAbs _ [] = []
relHistToThreadAbs currentAccs ((tid,relAcc):others) =
    let currentAcc = maybe 0 id $ lookup tid currentAccs
        newAcc = currentAcc + relAcc
        newLookup = (tid,newAcc):(filter ((/=) tid . fst) currentAccs)
    in (tid,newAcc):(relHistToThreadAbs newLookup others)

mkThreadAbsoluteHistory :: AccessNr -> [HistoryEntry] -> [(ThreadId, Integer)]
mkThreadAbsoluteHistory acc = relHistToThreadAbs [] . mkRelativeHistory acc

absHistSuffix :: History -> History -> Either String [(ThreadId, Integer)]
absHistSuffix prefix@(History (Finite pacc) _ _) hist =
    case stripSharedPrefix hist prefix of
      (hh, []) -> Right $ mkThreadAbsoluteHistory pacc hh
      _ -> Left $ (show prefix) ++ " is not a prefix of " ++ (show hist)
absHistSuffix _ _ = Left "tried to strip an infinite prefix"

threadAtAccess :: History -> AccessNr -> Either String ThreadId
threadAtAccess (History _ _ items) acc =
    foldr (\(HistoryRun tid acc') rest ->
               if (Finite acc) < acc'
               then Right tid
               else rest) (Left "ran out of history") $ dlToList items

instance Forcable HistoryEntry where
    force (HistorySetMemory _ r) = force r
    force x = seq x

instance Forcable History where
    force (History a b h) = force a . force b . force h

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
