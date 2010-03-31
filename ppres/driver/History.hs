{-# LANGUAGE MagicHash, RecursiveDo #-}
module History(
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
               initialHistory, destroyWorkerCache               
               ) where

import Control.Monad.Error
import Data.Word
import Data.IORef
import System.IO.Unsafe
import Network.Socket
import Data.List
import System.Posix.Signals
import IO
import Numeric
import Data.Bits
import GHC.Conc hiding (ThreadId)
import GHC.Base hiding (assert)
import System.Mem.Weak (addFinalizer)

import qualified Debug.Trace

import Types
import Util
import Socket
import Logfile
import Debug
import Config

data HistoryEntry = HistoryRun !ThreadId !(Topped AccessNr)
                  | HistorySetRegister !ThreadId !RegisterName !Word64
                  | HistoryAllocMemory !Word64 !Word64 !Word64
                  | HistorySetMemory !Word64 [Word8]
                  | HistorySetMemoryProtection !Word64 !Word64 !Word64
                  | HistorySetTsc !ThreadId !Word64
                  | HistoryAdvanceLog !LogfilePtr
                  | HistoryRunSyscall !ThreadId
                    deriving (Eq, Show, Read)
instance Render HistoryEntry where
    renderS (HistorySetMemory ptr bytes) suffix =
        ("HistorySetMemory 0x" ++ (showHex ptr "") ++ " " ++ (show $ length bytes)) ++ suffix
    renderS x s = shows x s

{- It is important that there be no references from HistoryWorker back
   to the matching History, so that the finalisers run at the right
   time. -}
data HistoryWorker = HistoryWorker { hw_dead :: TVar Bool,
                                     hw_worker :: IORef (Maybe Worker),
                                     hw_prev_lru :: TVar HistoryWorker,
                                     hw_next_lru :: TVar HistoryWorker,
                                     hw_is_root :: Bool }
data History = HistoryRoot HistoryWorker
             | History { hs_parent :: History,
                         hs_entry :: HistoryEntry,
                         hs_worker :: HistoryWorker,
                         hs_ident :: Integer }

allocateHistoryIdent :: IO Integer
allocateHistoryIdent = do wc <- workerCache
                          (res:newIdents) <- readIORef $ wc_idents wc
                          writeIORef (wc_idents wc) newIdents
                          return res
heListToHistory :: [HistoryEntry] -> History
heListToHistory [] = HistoryRoot rootHistory
heListToHistory (x:xs) =
    unsafePerformIO $ mdo d <- newTVarIO False
                          ww <- newIORef Nothing
                          p <- newTVarIO worker
                          n <- newTVarIO worker
                          ident <- allocateHistoryIdent
                          let worker = HistoryWorker { hw_dead = d,
                                                       hw_worker = ww,
                                                       hw_prev_lru = p,
                                                       hw_next_lru = n,
                                                       hw_is_root = False }
                          return $ History { hs_parent = heListToHistory xs,
                                             hs_entry = x,
                                             hs_worker = worker,
                                             hs_ident = ident }
instance Show History where
    show = show . historyGetHeList
instance Render History where
    render = render . historyGetHeList
instance Read History where
    readsPrec _ s = do (hes, trailer) <- reads s
                       return (heListToHistory $ reverse hes, trailer)
instance Eq History where
    (HistoryRoot _) == (HistoryRoot _) = True
    (HistoryRoot _) == _ = False
    _ == (HistoryRoot _) = False
    a == b =
        if a `unsafePtrEq` b
        then True
        else if hs_entry a == hs_entry b
             then hs_parent a == hs_parent b
             else False

data WorkerCache = WorkerCache { wc_logfile :: Logfile,
                                 wc_root :: HistoryWorker,
                                 wc_nr_workers :: TVar Int,
                                 wc_idents :: IORef [Integer] }
                                 
historyFold :: (a -> HistoryEntry -> a) -> a -> History -> a
historyFold _ base (HistoryRoot _) = base
historyFold folder base hist =
    folder (historyFold folder base (hs_parent hist)) (hs_entry hist)

history_logfile_ptr :: History -> LogfilePtr
history_logfile_ptr =
    historyFold (\acc ent ->
                      case ent of
                        HistoryAdvanceLog ptr -> ptr
                        _ -> acc) (LogfilePtr 0 0)

ioAssertTrue :: IO Bool -> IO ()
ioAssertTrue a = do a' <- a
                    assert "ioAssertTrue" a' $ return ()

doHistoryEntry :: Worker -> HistoryEntry -> IO ()
doHistoryEntry w (HistoryRun tid cntr) =
    do setThreadWorker w tid
       r <- runWorker "doHistoryEntry" w cntr
       when (not r) $
            putStrLn $ "failed to replay history entry run " ++ (show tid) ++ " " ++ (show cntr) ++ " in " ++ (show w)
doHistoryEntry w (HistorySetRegister tid reg val) =
    ioAssertTrue $ setRegisterWorker w tid reg val
doHistoryEntry w (HistoryAllocMemory addr size prot) =
    ioAssertTrue $ allocateMemoryWorker w addr size prot
doHistoryEntry w (HistorySetMemory addr bytes) =
    ioAssertTrue $ setMemoryWorker w addr bytes
doHistoryEntry w (HistorySetMemoryProtection addr size prot) =
    setMemoryProtectionWorker w addr size prot
doHistoryEntry w (HistorySetTsc tid tsc) =
    ioAssertTrue $ setTscWorker w tid tsc
doHistoryEntry w (HistoryAdvanceLog p) =
    setLogPtrWorker w p
doHistoryEntry w (HistoryRunSyscall t) =
    runSyscallWorker w t

rootHistory :: HistoryWorker
rootHistory = unsafePerformIO $ liftM wc_root workerCache

initialHistory :: Logfile -> Worker -> IO History
initialHistory lf w =
    do p <- newTVarIO undefined
       n <- newTVarIO undefined
       isDead <- newTVarIO False
       worker <- newIORef $ Just w
       let wrk = HistoryWorker { hw_dead = isDead, hw_worker = worker,
                                 hw_prev_lru = p, hw_next_lru = n, hw_is_root = True }
       atomically $ writeTVar p wrk
       atomically $ writeTVar n wrk
       nr <- newTVarIO 0
       idents <- newIORef [1..]
       let wc = WorkerCache { wc_logfile = lf, wc_root = wrk, wc_nr_workers = nr, wc_idents = idents}
       writeIORef globalWorkerCache wc
       return $ HistoryRoot wrk
               

privatiseWorker :: WorkerCache -> HistoryWorker -> STM Bool
privatiseWorker wc hw =
    do {- Remove from the list -}
       d <- readTVar $ hw_dead hw
       writeTVar (hw_dead hw) True
       when (not d) $
            do p <- readTVar $ hw_prev_lru hw
               n <- readTVar $ hw_next_lru hw
               writeTVar (hw_next_lru p) n
               writeTVar (hw_prev_lru n) p
               writeTVar (hw_prev_lru hw) hw
               writeTVar (hw_next_lru hw) hw
               nw <- readTVar $ wc_nr_workers wc
               writeTVar (wc_nr_workers wc) (nw - 1)
       return d

reallyKillHistoryWorker :: HistoryWorker -> IO ()
reallyKillHistoryWorker hw =
    do wrk <- readIORef $ hw_worker hw
       writeIORef (hw_worker hw) Nothing
       case wrk of
         Nothing -> error "Dead HW with no worker?"
         Just wrk' -> killWorker wrk'

killHistoryWorker :: WorkerCache -> HistoryWorker -> IO ()
killHistoryWorker wc hw =
    do alreadyDead <- atomically $ privatiseWorker wc hw
       when (not alreadyDead) $ reallyKillHistoryWorker hw

{- Finaliser for history objects -}
historyDead :: WorkerCache -> History -> IO ()
historyDead _ (HistoryRoot _) = error "root worker was garbage collected?"
historyDead wc hist =
    killHistoryWorker wc $ hs_worker hist

mkSimpleHistory :: History -> HistoryEntry -> History
mkSimpleHistory parent he =
    unsafePerformIO $ mdo w <- newIORef Nothing
                          dead <- newTVarIO True
                          p <- newTVarIO newWH
                          n <- newTVarIO newWH
                          wc <- workerCache
                          ident <- allocateHistoryIdent
                          let newWH = HistoryWorker { hw_dead = dead,
                                                      hw_worker = w,
                                                      hw_prev_lru = p,
                                                      hw_next_lru = n,
                                                      hw_is_root = False }
                              newHist = History { hs_parent = parent,
                                                  hs_entry = he,
                                                  hs_worker = newWH,
                                                  hs_ident = ident }
                          addFinalizer newHist (historyDead wc newHist)
                          return newHist

appendHistory :: History -> HistoryEntry -> History
appendHistory hist@(HistoryRoot _) he =
    mkSimpleHistory hist he
appendHistory hist he =
    case (he, hs_entry hist) of
      (HistoryRun hetid _, HistoryRun histtid _) 
          | hetid == histtid ->
              appendHistory (hs_parent hist) he
      (HistoryAdvanceLog _, HistoryAdvanceLog _)
          | he == hs_entry hist -> hist
      _ -> mkSimpleHistory hist he

stripNonRun :: History -> History
stripNonRun h@(HistoryRoot _) = h
stripNonRun hist =
    case hs_entry hist of
      HistoryRun _ _ -> hist
      _ -> stripNonRun $ hs_parent hist

{- Truncate a history so that it only runs to a particular epoch number -}
truncateHistory :: History -> Topped AccessNr -> Either String History
truncateHistory h@(HistoryRoot _) (Finite (AccessNr 0)) = Right h
truncateHistory (HistoryRoot _) _ = Left "truncate empty history"
truncateHistory hist cntr =
    case hs_entry hist of
      HistoryRun tid c | c == cntr -> Right hist
                       | c < cntr ->
                           Left "truncate tried to extend history"
                       | otherwise ->
                           case stripNonRun (hs_parent hist) of
                             (HistoryRoot _) ->
                                 Right $ appendHistory (hs_parent hist) (HistoryRun tid cntr)
                             runParent ->
                                 case hs_entry runParent of
                                   HistoryRun _ c'
                                     | c' >= cntr ->
                                         truncateHistory runParent cntr
                                     | otherwise ->
                                         Right $ appendHistory (hs_parent hist) (HistoryRun tid cntr)
                                   _ -> error "stripNonRun misbehaving"
      _ ->
          case stripNonRun (hs_parent hist) of
            (HistoryRoot _) ->
                if cntr == (Finite $ AccessNr 0)
                then Right hist
                else Left "truncate history with only non-run entries"
            runParent ->
                case hs_entry runParent of
                  HistoryRun _ c'
                    | c' >= cntr ->
                        truncateHistory runParent cntr
                    | otherwise ->
                        Left "truncate tried to extend history (ends in non-run)"
                  _ -> error "stripNonRun misbehaving"
threadAtAccess :: History -> AccessNr -> Either String ThreadId
threadAtAccess hist acc =
    historyFold (\rest (HistoryRun tid acc') ->
                     if (Finite acc) < acc'
                     then Right tid
                     else rest) (Left "ran out of history") hist

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
traceTo' worker tracer ((HistoryAdvanceLog ptr):rest) =
    do setLogPtrWorker worker ptr
       traceTo' worker tracer rest
traceTo' worker tracer ((HistoryRunSyscall tid):rest) =
    do runSyscallWorker worker tid
       traceTo' worker tracer rest

historyGetHeList :: History -> [HistoryEntry]
historyGetHeList = reverse . historyFold (flip (:)) []

unsafePtrEq :: a -> a -> Bool
unsafePtrEq a b = (unsafeCoerce# a) `eqAddr#` (unsafeCoerce# b)

getDeltaScript :: History -> History -> Maybe [HistoryEntry]
getDeltaScript (HistoryRoot _) end = Just $ historyGetHeList end
getDeltaScript _ (HistoryRoot _) = Nothing
getDeltaScript start end =
    let quick s e =
            if s `unsafePtrEq` e
            then Just []
            else case quick s (hs_parent e) of
                   Just b -> Just $ (hs_entry end):b
                   Nothing -> Nothing
    in case quick start end of
         Just r -> Just $ reverse r
         Nothing ->
             {- start isn't on the path from the root to end.  Do it
                the hard way. -}
             Debug.Trace.trace "getDeltaScript on slow path..." $
             let start' = historyGetHeList start
                 end' = historyGetHeList end
                 worker [] xs = Just xs
                 worker _ [] = Nothing
                 worker aas@(a:as) bbs@(b:bs)
                     | a == b = worker as bs
                     | otherwise =
                         case (a, b) of
                           (HistoryRun atid acntr,
                            HistoryRun btid bcntr)
                               | atid == btid ->
                                   if acntr < bcntr
                                   then worker as bbs
                                   else worker aas bs
                           _ -> Nothing
             in worker start' end'

traceTo'' :: (Worker -> ThreadId -> Topped AccessNr -> IO [a]) -> Worker -> History -> History -> IO (Either String [a])
traceTo'' tracer worker start end =
    case getDeltaScript start end of
      Just todo -> liftM Right $ traceTo' worker tracer todo
      Nothing -> return $ Left $ shows start $ " is not a prefix of " ++ (show end)

{- Take a worker and a history representing its current state and run
   it forwards to some other history, logging control expressions as
   we go. -}
controlTraceToWorker :: Worker -> History -> History -> IO (Either String [Expression])
controlTraceToWorker = traceTo'' controlTraceWorker

traceToWorker :: Worker -> History -> History -> IO (Either String [TraceRecord])
traceToWorker = traceTo'' traceWorker

sendWorkerCommand :: Worker -> ControlPacket -> IO ResponsePacket
sendWorkerCommand worker cp =
    do a <- readIORef $ worker_alive worker
       if not a
        then error $ "send command " ++ (show cp) ++ " to dead worker on fd " ++ (show $ worker_fd worker)
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

setLogPtrPacket :: LogfilePtr -> ControlPacket
setLogPtrPacket (LogfilePtr p n) = ControlPacket 0x124b [fromIntegral p, fromInteger n]

runSyscallPacket :: ThreadId -> ControlPacket
runSyscallPacket (ThreadId tid) = ControlPacket 0x124c [fromInteger tid]

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
                  modifyIORef nrForkedWorkers $ \x -> x - 1
          else error "can't kill worker?"

freezeWorker :: Worker -> IO ()
freezeWorker worker =
    writeIORef (worker_frozen worker) True

workerFrozen :: Worker -> IO Bool
workerFrozen = readIORef . worker_frozen

mustBeThawed :: String -> Worker -> IO ()
mustBeThawed m w = do t <- workerFrozen w
                      assert ("worker frozen unexpectedly: " ++ m) (not t) $ return ()

runWorker :: String -> Worker -> Topped AccessNr -> IO Bool
runWorker msg worker acc = mustBeThawed ("runWorker: " ++ msg) worker >> trivCommand worker (runPacket acc)

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
                                trc_load_in_monitor = other_args!!3 /= 0,
                                trc_rip = other_args!!4 }, rs)
              5 -> (TraceStore { trc_store_val = fromIntegral $ other_args!!0,
                                 trc_store_size = fromIntegral $ other_args!!1,
                                 trc_store_ptr = fromIntegral $ other_args!!2,
                                 trc_store_in_monitor = other_args!!3 /= 0,
                                 trc_rip = other_args!!4 }, rs)
              6 -> (case head rs of
                      ResponseDataString s -> TraceCalling s
                      _ -> error $ "mangled trace calling: " ++ (show other_args) ++ ", " ++ (show rs), tail rs)
              7 -> (case head rs of
                      ResponseDataString s -> TraceCalled s
                      _ -> error $ "mangled trace called: " ++ (show other_args) ++ ", " ++ (show rs), tail rs)
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
    do mustBeThawed "traceCmd" worker
       (ResponsePacket _ args) <- sendWorkerCommand worker pkt
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
                newFrozen <- newIORef False
                modifyIORef nrForkedWorkers $ (+) 1
                return $ Just $ Worker {worker_fd = newFd, worker_alive = newAlive, worker_frozen = newFrozen }
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
       mustBeThawed "controlTraceWorker" worker
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
        validateHistory [ResponseDataAncillary 19 [0]] _ = True
        validateHistory ((ResponseDataAncillary 19 [0x1236, tid, acc]):o) o's@((HistoryRun tid' acc'):o')
            | (ThreadId $ toInteger tid) == tid' =
                case (Finite $ AccessNr $ toInteger acc) `compare` acc' of
                  LT -> validateHistory o o's
                  EQ -> validateHistory o o'
                  GT -> Debug.Trace.trace ("history validation failed because worker was at " ++ (show acc) ++ " and we only wanted " ++ (show acc') ++ ", rest " ++ (show o')) False
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
                        ((HistorySetTsc (ThreadId tid') tsc'):o')
            | toInteger tid == tid' && tsc == tsc' = validateHistory o o'
        validateHistory ((ResponseDataAncillary 19 [0x124b, p, n]):o)
                        ((HistoryAdvanceLog (LogfilePtr p' n')):o')
            | p == (fromIntegral p') && n == (fromInteger n') = validateHistory o o'
        validateHistory ((ResponseDataAncillary 19 [0x124c, t]):o)
                        ((HistoryRunSyscall (ThreadId t')):o')
            | t == (fromIntegral t') = validateHistory o o'
        validateHistory o o' = Debug.Trace.trace ("history validation failed: " ++ (show o) ++ " vs " ++ (show o')) False
    in do (ResponsePacket _ params) <- sendWorkerCommand worker getHistoryPacket
          let r = validateHistory params desired_hist
          when (not r) $ putStrLn $ "validation of " ++ (show desired_hist) ++ " against " ++ (show params) ++ " in " ++ (show worker) ++ " failed"
          return r

setLogPtrWorker :: Worker -> LogfilePtr -> IO ()
setLogPtrWorker w p = do trivCommand w $ setLogPtrPacket p
                         return ()

{- Pull a WCE to the front of the LRU list -}
touchWorkerCacheEntry :: HistoryWorker -> IO ()
touchWorkerCacheEntry hw =
    if hw_is_root hw
    then return ()
    else do wc <- workerCache
            atomically $ do {- Remove from old place -}
                            prev <- readTVar $ hw_prev_lru hw
                            next <- readTVar $ hw_next_lru hw
                            writeTVar (hw_next_lru prev) next
                            writeTVar (hw_prev_lru next) prev

                            {- Insert in new place -}
                            let newPrev = wc_root wc
                            newNext <- readTVar (hw_next_lru newPrev)
                            writeTVar (hw_next_lru newPrev) hw
                            writeTVar (hw_prev_lru newNext) hw
                            writeTVar (hw_next_lru hw) newNext
                            writeTVar (hw_prev_lru hw) newPrev

assert :: String -> Bool -> a -> a
assert _ True = id
assert msg False = unsafePerformIO $ dumpLog >> (error $ "assertion failure: " ++ msg)

fixupWorkerCache :: WorkerCache -> IO ()
fixupWorkerCache wc =
    do w <- atomically $ do n <- readTVar $ wc_nr_workers wc
                            if n <= cacheSize
                             then return Nothing
                             else do targ <- readTVar $ hw_prev_lru $ wc_root wc
                                     dead <-
                                         assert ("nr_workers " ++ (show n) ++ " but no workers found") (not $ hw_is_root targ) $
                                         privatiseWorker wc targ
                                     assert "dead worker on list" (not dead) $
                                         return $ Just targ
       case w of
         Just w' -> reallyKillHistoryWorker w' >> fixupWorkerCache wc
         Nothing -> return ()

cacheSize :: Int
cacheSize = 900

globalWorkerCache :: IORef WorkerCache
{-# NOINLINE globalWorkerCache #-}
globalWorkerCache =
    unsafePerformIO $ newIORef $ error "use of worker cache before it was ready?"

nrForkedWorkers :: IORef Int
nrForkedWorkers =
    unsafePerformIO $ newIORef 1

workerCache :: IO WorkerCache
workerCache =
    do wc <- readIORef globalWorkerCache
       pending <- getPendingSignals
       when (sigUSR1 `inSignalSet` pending) $
            do dumpLog
               unblockSignals $ addSignal sigUSR1 emptySignalSet
               blockSignals $ addSignal sigUSR1 emptySignalSet
       return wc

destroyWorkerCache :: IO ()
destroyWorkerCache =
    do wc <- workerCache
       killAllWorkers wc
       where killAllWorkers wc =
                 do targ <-
                        atomically $ do t <- readTVar $ hw_next_lru $ wc_root wc
                                        if hw_is_root t
                                         then return Nothing
                                         else do privatiseWorker wc t
                                                 return $ Just t
                    case targ of
                      Nothing -> return ()
                      Just t -> do reallyKillHistoryWorker t
                                   killAllWorkers wc

reallySnapshot :: Worker -> IO Worker
reallySnapshot w =
    do w' <- takeSnapshot w
       case w' of
         Nothing -> error "cannot take a snapshot"
         Just w'' -> return w''

modifyTVar :: TVar a -> (a -> a) -> STM ()
modifyTVar v f =
    do v' <- readTVar v
       writeTVar v $ f v'

addWorkerToLRU :: HistoryWorker -> Worker -> IO ()
addWorkerToLRU hw worker =
    do wc <- workerCache
       writeIORef (hw_worker hw) $ Just worker
       atomically $ let newPrev = wc_root wc in
                    do writeTVar (hw_dead hw) False
                       newNext <- readTVar (hw_next_lru newPrev)
                       writeTVar (hw_next_lru newPrev) hw
                       writeTVar (hw_prev_lru newNext) hw
                       writeTVar (hw_next_lru hw) newNext
                       writeTVar (hw_prev_lru hw) newPrev
                       modifyTVar (wc_nr_workers wc) ((+) 1)

getWorker' :: Bool -> History -> IO Worker
getWorker' pure (HistoryRoot w) =
    do w' <- readIORef $ hw_worker w
       w'' <- case w' of
                Nothing -> error "root HW lost its worker"
                Just w''' -> return w'''
       if pure
        then return w''
        else reallySnapshot w''
getWorker' pure hist =
    do w <- readIORef $ hw_worker $ hs_worker hist
       case w of
         Just w' -> do touchWorkerCacheEntry (hs_worker hist)
                       if pure
                        then return w'
                        else reallySnapshot w'
         Nothing ->
             do worker <- getWorker' False $ hs_parent hist
                doHistoryEntry worker (hs_entry hist)
                freezeWorker worker
                addWorkerToLRU (hs_worker hist) worker
                wc <- workerCache
                fixupWorkerCache wc
                if pure
                 then return worker
                 else reallySnapshot worker

getWorker :: Bool -> History -> IO Worker
getWorker pure hist =
    do r <- getWorker' pure hist
       v <- validateHistoryWorker r (historyGetHeList hist)
       wc <- assert ("getWorker' returned bad worker for history " ++ (show hist)) v workerCache
       fixupWorkerCache wc
       return r

impureCmd :: (Worker -> IO a) -> History -> a
impureCmd w hist =
    unsafePerformIO $ do worker <- getWorker False hist
                         res <- w worker
                         killWorker worker
                         return res

queryCmd :: (Worker -> IO a) -> History -> a
queryCmd w hist =
    unsafePerformIO $ getWorker True hist >>= w

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
    impureCmd (\worker -> controlTraceToWorker worker start end) start

traceTo :: History -> History -> Either String [TraceRecord]
traceTo start end = 
    impureCmd (\worker -> traceToWorker worker start end) start

getRegisters :: History -> RegisterFile
getRegisters = queryCmd getRegistersWorker

getRipAtAccess :: History -> AccessNr -> Either String Word64
getRipAtAccess hist whn =
    do hist' <- truncateHistory hist $ Finite $ whn + 1
       getRegister (getRegisters hist') REG_RIP

traceToEvent :: History -> ThreadId -> Topped AccessNr -> Either String ([TraceRecord], History)
traceToEvent start tid limit =
    unsafePerformIO $ do worker <- getWorker False start
                         trc <- traceToEventWorker worker tid limit
                         rs <- replayStateWorker worker
                         killWorker worker
                         return $ let finalHist = appendHistory start $ HistoryRun tid $ Finite $ rs_access_nr rs
                                  in Right (trc, finalHist)

runThreadToEventWorker :: Worker -> History -> ThreadId -> Topped AccessNr -> IO (TraceRecord, History, ReplayState)
runThreadToEventWorker worker start tid limit =
    do trc <- traceToEventWorker worker tid limit
       rs <- replayStateWorker worker
       let newHist = appendHistory start $ HistoryRun tid $ Finite $ rs_access_nr rs
       return (last trc, newHist, rs)

runSyscallWorker :: Worker -> ThreadId -> IO ()
runSyscallWorker worker tid =
    do trivCommand worker $ runSyscallPacket tid
       return ()

runThread :: Logfile -> History -> ThreadId -> Topped AccessNr -> Either String History
runThread logfile hist tid acc =
    unsafePerformIO $ do worker <- getWorker False hist
                         mustBeThawed "runThread" worker
                         (evt, newHist, rs) <- runThreadToEventWorker worker hist tid acc
                         case rs of
                           ReplayStateOkay acc' ->
                               if Finite acc' <= acc
                               then do let lp = history_logfile_ptr hist
                                           fixedHist =
                                              case nextRecord logfile lp of
                                                Nothing ->
                                                    error "unexpected end of log when worker thought there was more?"
                                                Just (logrecord, nextLogPtr) ->
                                                    let success = return . Right
                                                        justAdvance = success (advanceLog newHist nextLogPtr, True)
                                                        failed = return . Left
                                                        
                                                        {- Go and process all the populate memory records which come
                                                           after logptr. -}
                                                        processPopMemRecords pphist logptr =
                                                            case nextRecord logfile logptr of
                                                              Just (LogRecord _ (LogMemory ptr contents), nlp) ->
                                                                  processPopMemRecords (setMemory pphist ptr contents) nlp
                                                              _ -> (pphist, logptr)

                                                        {- syscalls which we handle by just re-running them -}
                                                        replaySyscall (LogSyscall sysnr _ _ _ _)
                                                            | sysnr `elem` [10, 11, 12, 13, 14, 158, 273] =
                                                                (runSyscall newHist $ trc_tid evt, nextLogPtr)

                                                        {- syscalls which we handle by just imposing the return value -}
                                                        replaySyscall (LogSyscall sysnr sysres _ _ _)
                                                            | sysnr `elem` [0, 1, 2, 3, 4, 5, 21, 63, 79, 97, 102, 202] =
                                                                (setRegister newHist (trc_tid evt) REG_RAX sysres, nextLogPtr)

                                                        {- syscalls which we handle by re-running and then imposing the
                                                           recorded return value. -}
                                                        replaySyscall (LogSyscall sysnr sysres _ _ _)
                                                            | sysnr `elem` [56, 218] =
                                                            (setRegister (runSyscall newHist $ trc_tid evt) (trc_tid evt) REG_RAX sysres,
                                                             nextLogPtr)

                                                        {- exit_group.  Ignore it and move to the next record, which should
                                                           immediately finish the log. -}
                                                        replaySyscall (LogSyscall 231 _ _ _ _) =
                                                            (newHist, nextLogPtr)

                                                        {- mmap -}
                                                        replaySyscall (LogSyscall 9 sysres _ len prot) =
                                                            let (doneMmapHist, finalLogPtr) =
                                                                    if sysres > 0xffffffffffff8000
                                                                    then {- syscall failed -> just replay the failure -}
                                                                        (newHist, nextLogPtr)
                                                                    else {- syscall succeeded -> have to replay it properly -}
                                                                        let addr = sysres
                                                                            allocMem = allocateMemory newHist addr len (prot .|. 2) {- Turn on write access -}
                                                                            (populateMem, ptrAfterPopulateMem) =
                                                                                processPopMemRecords allocMem nextLogPtr
                                                                            resetProt =
                                                                                if prot .&. 2 == 0
                                                                                then populateMem
                                                                                else setMemoryProtection populateMem addr len prot
                                                                        in (resetProt, ptrAfterPopulateMem)
                                                            in (setRegister doneMmapHist (trc_tid evt) REG_RAX sysres, finalLogPtr)

                                                        replaySyscall (LogSyscall sysnr _ _ _ _) =
                                                            error $ "don't know how to replay syscall " ++ (show sysnr)

                                                        replaySyscall _ = error "replaySyscall called on non-syscall?"

                                                        replaySyscall' x =
                                                            let (h, np) = replaySyscall x
                                                                (h', np') = processPopMemRecords h np
                                                            in advanceLog h' np'
                                                        res =
                                                            case (trc_trc evt, lr_body logrecord) of
                                                              (TraceRdtsc, LogRdtsc tsc) ->
                                                                  success (advanceLog (setTsc newHist tid tsc) nextLogPtr, True)
                                                              (TraceRdtsc, r) ->
                                                                  failed $ "rdtsc event with record " ++ (show r)
                                                              (TraceCalling _, LogClientCall) -> justAdvance
                                                              (TraceCalling n, r) ->
                                                                  failed $ "calling " ++ n ++ " event with record " ++ (show r)
                                                              (TraceCalled _, LogClientReturn) -> justAdvance
                                                              (TraceCalled n, r) ->
                                                                  failed $ "called " ++ n ++ " event with record " ++ (show r)
                                                              (TraceLoad val sz ptr _ _, LogAccess True val' sz' ptr') |
                                                                  sz == sz' && ptr == ptr' && val == val' ->
                                                                  justAdvance
                                                              (TraceLoad _ _ _ _ _, _) | useMemoryRecords ->
                                                                  failed $ "load event " ++ (show evt) ++ " against record " ++ (show logrecord)
                                                              (TraceStore val sz ptr _ _, LogAccess False val' sz' ptr') |
                                                                  sz == sz' && ptr == ptr' && val == val' ->
                                                                  justAdvance
                                                              (TraceStore _ _ _ _ _, _) | useMemoryRecords ->
                                                                  failed $ "store event " ++ (show evt) ++ " against record " ++ (show logrecord)
                                                              (TraceSignal rip signr err va, LogSignal rip' signr' err' va') |
                                                                  and [rip == rip', signr == (fromIntegral signr'), err == err', va == va'] ->
                                                                  justAdvance
                                                              (TraceSignal _ _ _ _, _) ->
                                                                  failed $ "signal event " ++ (show evt) ++ " against record " ++ (show logrecord)
                                                              (TraceSyscall sysnr, LogSyscall sysnr' _ arg1 arg2 arg3) ->
                                                                  Debug.Trace.trace ("validate syscall " ++ (show evt)) $
                                                                  do regs <- getRegistersWorker worker
                                                                     let rdi = getRegister' regs REG_RDI
                                                                         rsi = getRegister' regs REG_RSI
                                                                         rdx = getRegister' regs REG_RDX
                                                                     if rdi == arg1 && rsi == arg2 && rdx == arg3 && sysnr == (fromIntegral sysnr')
                                                                      then return $ Right (replaySyscall' $ lr_body logrecord, True)
                                                                      else failed $ "syscall record " ++ (show logrecord) ++ " against trace event " ++ (show evt) ++ " " ++
                                                                                    (showHex rdi $ " " ++ (showHex rsi $ " " ++ (showHex rdx "")))
                                                              (TraceSyscall _, _) ->
                                                                  failed $ "syscall event " ++ (show evt) ++ " against record " ++ (show logrecord)
                                                              (TraceEnterMonitor, _) -> success (newHist, False)
                                                              (TraceExitMonitor, _) -> success (newHist, False)
                                                              (TraceFootstep _ _ _ _, _) -> success (newHist, False)
                                                              (TraceLoad _ _ _ _ _, _) -> success (newHist, False)
                                                              (TraceStore _ _ _ _ _, _) -> success (newHist, False)
                                                    in do r <- res
                                                          case r of
                                                            Left e -> failed e
                                                            Right (res', checkThread) ->
                                                             if checkThread && trc_tid evt /= lr_tid logrecord
                                                             then failed $ "wrong thread: wanted " ++ (show logrecord) ++ ", got " ++ (show evt)
                                                             else success res'
                                       fixedHist' <- fixedHist
                                       killWorker worker
                                       return $ case fixedHist' of
                                                  Left e -> Left e
                                                  Right fh' ->
                                                      if Finite acc' == acc
                                                      then fixedHist'
                                                      else runThread logfile fh' tid acc
                               else do killWorker worker
                                       return $ Right newHist
                           _ -> do killWorker worker
                                   return $ Right newHist

setRegister :: History -> ThreadId -> RegisterName -> Word64 -> History
setRegister hist tid reg val =
    appendHistory hist $ HistorySetRegister tid reg val

allocateMemory :: History -> Word64 -> Word64 -> Word64 -> History
allocateMemory hist addr size prot =
    appendHistory hist $ HistoryAllocMemory addr size prot

setMemory :: History -> Word64 -> [Word8] -> History
setMemory hist addr contents =
    appendHistory hist $ HistorySetMemory addr contents

setMemoryProtection :: History -> Word64 -> Word64 -> Word64 -> History
setMemoryProtection hist addr size prot =
    appendHistory hist $ HistorySetMemoryProtection addr size prot

setTsc :: History -> ThreadId -> Word64 -> History
setTsc hist tid tsc = appendHistory hist $ HistorySetTsc tid tsc

advanceLog :: History -> LogfilePtr -> History
advanceLog hist lp = appendHistory hist $ HistoryAdvanceLog lp

runSyscall :: History -> ThreadId -> History
runSyscall hist tid = appendHistory hist $ HistoryRunSyscall tid
