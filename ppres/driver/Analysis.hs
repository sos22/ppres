{-# LANGUAGE RecursiveDo #-}
module Analysis(findRacingAccesses, findControlFlowRaces, 

                {- I don't actually use these at the moment, but will
                   do soon, and I want to make sure they at least keep
                   compiling without getting lots of stupid compiler
                   errors. -}
                evalExpressionInSnapshot, evalExpressionWithStore,
                enumerateHistories',

                enumerateHistories, getRacingExpressions,
                criticalSections, mkFixupLibrary) where

import Types
import WorkerCache
import History
import ReplayState()
import Timing
import Util

import Data.Bits
import Data.Word
import Data.List
import Numeric

import qualified Debug.Trace

dt :: String -> a -> a
dt = Debug.Trace.trace

{- We have two traces, A and B.  A represents what actually happened,
   and B an estimate of what we could have done by running some other
   thread.  A pair of accesses races if one is a load in A from some
   address X and the other is a store to X from B, and the values in
   the two accesses are different.  This function finds all critical
   access pairs, in some undefined order. -}

findRacingAccesses :: [TraceRecord] -> [TraceRecord] -> [(TraceRecord, TraceRecord)]
findRacingAccesses a b =
    let aLoads = [r | r@(TraceRecord (TraceLoad _ _ _ _) _) <- a]
        bStores = [r | r@(TraceRecord (TraceStore _ _ _ _) _) <- b]
        storesTo ptr = [r | r <- bStores, ptr == (trc_store_ptr $ trc_trc r)]
        res = [(load, store)
               |
               load <- aLoads,
               store <- storesTo (trc_load_ptr $ trc_trc load),
               (trc_load_val $ trc_trc load) /= (trc_store_val $ trc_trc store)
              ]
    in res

{- Given a list of pairs of racing accesses and a list of expressions
   on which control flow depends, find all of the races which might
   have influenced control flow. -}

findControlFlowRaces :: [(TraceRecord, TraceRecord)] -> [Expression] -> [(TraceRecord, TraceRecord)]
findControlFlowRaces races expressions =
    filter isRelevant races
    where isRelevant (load, _) = or $ map (expressionMentionsLoad load) expressions
          expressionMentionsLoad _ (ExpressionRegister _ _) = False
          expressionMentionsLoad _ (ExpressionConst _) = False
          expressionMentionsLoad _ (ExpressionImported _ ) = False
          expressionMentionsLoad e (ExpressionBinop _ x y) = expressionMentionsLoad e x || expressionMentionsLoad e y
          expressionMentionsLoad e (ExpressionNot x) = expressionMentionsLoad e x
          expressionMentionsLoad (TraceRecord (TraceLoad _ _ _ _) loc1)
                                     (ExpressionLoad _ _ loc2 _ _) = loc1 == loc2
          expressionMentionsLoad _ _ = error "confused"


wordSigned :: Word64 -> Integer
wordSigned w =
    if w `testBit` 63
    then (fromIntegral w) - 0x10000000000000000
    else (fromIntegral w)

binopFunc :: Binop -> Word64 -> Word64 -> Word64
binopFunc op = case op of
                 BinopSub -> (-)
                 BinopAdd -> (+)
                 BinopMull -> (*)
                 BinopAnd -> (.&.)
                 BinopOr -> (.|.)
                 BinopXor -> xor
                 _ -> \l r -> case op of
                                BinopMullHi -> fromInteger $ (toInteger l * toInteger r) `shiftR` 64
                                BinopShrl -> fromInteger $ (toInteger l) `shiftR` (fromIntegral r)
                                BinopShl -> l `shiftL` (fromIntegral r)
                                BinopShra -> l `shiftR` (fromIntegral r)
                                BinopLe -> if wordSigned l <= wordSigned r then 1 else 0
                                BinopBe -> if l <= r then 1 else 0
                                BinopEq -> if l == r then 1 else 0
                                BinopB -> if l < r then 1 else 0
                                BinopMullS -> error "Write me"
                                BinopCombine -> error "can't eval combine"
                                _ -> error "can't happen"

evalExpressionWithStore :: Expression -> [(Word64, Word64)] -> Maybe Word64
evalExpressionWithStore (ExpressionRegister _ n) _ = Just n
evalExpressionWithStore (ExpressionConst n) _ = Just n
evalExpressionWithStore (ExpressionLoad _ _ _ addr val) st =
    do addr' <- evalExpressionWithStore addr st
       val' <- evalExpressionWithStore val st
       return $ case lookup addr' st of
                  Nothing -> val'
                  Just v -> v
evalExpressionWithStore (ExpressionStore _ _ val) st =
    evalExpressionWithStore val st
evalExpressionWithStore (ExpressionImported v) _ = Just v
evalExpressionWithStore (ExpressionNot e) st =
    fmap complement $ evalExpressionWithStore e st
evalExpressionWithStore (ExpressionBinop BinopCombine _ _) _ = Nothing
evalExpressionWithStore (ExpressionBinop op l' r') st =
    do l <- evalExpressionWithStore l' st
       r <- evalExpressionWithStore r' st
       return $ binopFunc op l r

traceThread :: History -> ThreadId -> [TraceRecord]
traceThread start thr =
    case histCoord start of
      Infinity -> []
      Finite cur_record ->
          let new_record = ReplayCoord { rc_access = rc_access cur_record + 50000 }
          in snd $ deError $ trace (deError $ appendHistory start $ HistorySetThread thr) $ Finite new_record

runMemoryThread :: History -> ThreadId -> AccessNr -> (History, [TraceRecord])
runMemoryThread start tid acc =
    let targetCoord = ReplayCoord acc
    in deError $ trace (deError $ appendHistory start (HistorySetThread tid)) $ Finite targetCoord

fetchMemory8 :: History -> Word64 -> Maybe Word64
fetchMemory8 hist addr =
    do xs <- fetchMemory hist addr 8
       return $ fromInteger $ foldr (\a b -> b * 256 + a) 0 $ map toInteger xs

evalExpressionInSnapshot :: Expression -> History -> [(Word64, Word64)] -> Maybe Word64
evalExpressionInSnapshot (ExpressionRegister _ n) _ _ = Just n
evalExpressionInSnapshot (ExpressionConst n) _ _ = Just n
evalExpressionInSnapshot (ExpressionLoad _ _ _ addr _) hist stores =
    do addr' <- evalExpressionInSnapshot addr hist stores
       case lookup addr' stores of
         Nothing -> fetchMemory8 hist addr'
         Just v -> Just v
evalExpressionInSnapshot (ExpressionStore _ _ val) hist stores =
    evalExpressionInSnapshot val hist stores
evalExpressionInSnapshot (ExpressionImported v) _ _ = Just v
evalExpressionInSnapshot (ExpressionBinop BinopCombine _ _) _ _ = Nothing
evalExpressionInSnapshot (ExpressionBinop op l' r') hist st =
    do l <- evalExpressionInSnapshot l' hist  st
       r <- evalExpressionInSnapshot r' hist st
       return $ binopFunc op l r
evalExpressionInSnapshot (ExpressionNot l) hist st =
    fmap complement $ evalExpressionInSnapshot l hist st

{- Standard queue structure -- head is in the right order, tail is
   reversed, giving fast append-tail and pop-head operations. -}
data Queue a = Queue { q_head :: [a],
                       q_tail :: [a] }

emptyQueue :: Queue a
emptyQueue = Queue [] []

appendQueue :: a -> Queue a -> Queue a
appendQueue item q = q { q_tail = item:(q_tail q) }

queuePop :: Queue a -> Maybe (a, Queue a)
queuePop q =
    case q_head q of
      (a:as) -> Just (a, q { q_head = as })
      [] ->
          case q_tail q of
            [] -> Nothing
            _ -> queuePop $ q { q_head = reverse $ q_tail q,
                                q_tail = [] }

queueToList :: Queue a -> [a] -> [a]
queueToList q trail =
    (q_head q) ++ (reverse $ q_tail q) ++ trail

singletonQueue :: a -> Queue a
singletonQueue i = appendQueue i emptyQueue

histCoord :: History -> Topped ReplayCoord
histCoord hist = case histLastCoord hist of
                   Finite x -> Finite x
                   Infinity ->
                       case replayState hist of
                         ReplayStateOkay x -> Finite x
                         ReplayStateFinished _ -> Infinity
                         ReplayStateFailed _ _ e _ -> Finite e

instance Show a => Show (Queue a) where
    show x = "Queue " ++ (show $ queueToList x [])

{- We use a breadth-first search locally, and depth-first globally.
   The idea is that you start off doing breadth first, and then if you
   advance a long way you switch to depth first.  This is implemented
   by having a current generation of replay points which is maintained
   as a queue and a backlog list which is maintained as a stack.  If
   we try to add a new state which is more than some number of epochs
   ahead of the current state then we flush the queue to the stack and
   start a new queue.  When we need to pick a state, we grab the queue
   first, if it's non-empty, and then fall back to the stack if
   there's nothing available there. -}
data EnumerationState = EnumerationState {ens_stack :: [(ReplayCoord, History)],
                                          ens_queue :: Queue (ReplayCoord, History),
                                          ens_current :: History,
                                          ens_finished :: Bool } deriving Show

addEnumState :: ReplayCoord -> History -> EnumerationState -> EnumerationState
addEnumState origin new es =
    if ens_finished es
    then es
    else
        let currentEpoch = histCoord $ ens_current es
            newEpoch = origin
            flushQueue =
                case currentEpoch of
                  Finite currentEpoch' ->
                      rc_access newEpoch > rc_access currentEpoch' - 100
                  _ -> False

            new_stack = if flushQueue
                        then queueToList (ens_queue es) (ens_stack es)
                        else ens_stack es
            new_queue = if flushQueue
                        then singletonQueue (origin, new)
                        else appendQueue (origin, new) $ ens_queue es
        in es { ens_stack = new_stack,
                ens_queue = new_queue }

addEnumStates :: ReplayCoord -> [History] -> EnumerationState -> EnumerationState
addEnumStates origin xs es = foldr (addEnumState origin) es xs

enumStateFinished :: History -> EnumerationState
enumStateFinished hist = EnumerationState {ens_stack = [],
                                           ens_queue = emptyQueue,
                                           ens_current = hist,
                                           ens_finished = True}

getNextExploreState :: EnumerationState -> Maybe (History, EnumerationState)
getNextExploreState es =
    case queuePop $ ens_queue es of
      Nothing ->
          case ens_stack es of
            [] -> Nothing
            ((_,a):as) -> Just (a, es { ens_stack = as })
      Just ((_,a), new_queue) ->
          Just (a, es {ens_queue = new_queue})

live_threads :: History -> [ThreadId]
live_threads hist =
    [a | (a, b) <- threadState hist, not (ts_dead b || ts_blocked b)]

{- Enumerate all ``interesting'' small-step advances we can make from
   this state.  We stop as soon as we find a replay which succeeds.
   The ``default'' action, of just running the trace-selected thread
   to the end of the epoch, is implicitly handled by the big step
   advancer, so we don't need to deal with that here (and in fact we
   don't need to consider any epoch-crossing actions at all).

   We filter out un-interesting memory accesses by looking for races.
   A race is a pair of accesses, A and B, issued by different threads
   in this epoch where at least one is a store.  For each thread with
   a racing access, we need to emit a single schedule which runs that
   thread up to and including the *first* racing access.  We don't
   need to emit anything for threads which don't have any races in
   them.
-}
enumerateHistoriesSmallStep :: History -> EnumerationState -> EnumerationState
enumerateHistoriesSmallStep start trailer =
    case replayState start of
      ReplayStateFailed _ _ _ _ -> trailer
      ReplayStateFinished _ -> enumStateFinished start
      ReplayStateOkay origin ->
          let threads = live_threads start
              trace_for_thread t = traceThread start t
              footstep_is_mem (TraceLoad _ _ _ False) = True
              footstep_is_mem (TraceStore _ _ _ False) = True
              footstep_is_mem _ = False
              memtrace_for_thread' = filter (footstep_is_mem . trc_trc) . trace_for_thread
              thread_traces = zip threads $ map memtrace_for_thread' threads
              memtrace_for_thread m t =
                  case lookup t thread_traces of
                    Just x -> x
                    Nothing -> error $ "lost a thread somewhere, wanted " ++ (show t) ++ ", had " ++ (show thread_traces) ++ " (" ++ m ++ ")"

              {- A list of racing accesses which we want to
                 investigate in this thread.  An entry (x, y) in the
                 list means to run thread t to access x and then
                 switch to thread y.  We only need to consider one x
                 for each y, and it will be the earliest access such
                 that access x in this thread races with some access
                 in thread y. -}

              racing_access_for_thread :: ThreadId -> [(AccessNr, ThreadId)]
              racing_access_for_thread t =
                  let races_with_thread t' =
                          let racingAccesses =
                                  filter (isRace . trc_trc) $ memtrace_for_thread ("t = " ++ (show t) ++ ", t' " ++ (show t')) t
                                  where isRace (TraceLoad _ _ ptr _) =
                                            or $ map (isStore . trc_trc) $ overlapping_accesses ptr
                                        isRace (TraceStore _ _ ptr _) =
                                            case overlapping_accesses ptr of
                                              [] -> False
                                              _ -> True
                                        isRace _ = False
                                        isStore (TraceStore _ _ _ _) = True
                                        isStore _ = False
                                        overlapping_accesses ptr = filter (access_overlaps . trc_trc) $ memtrace_for_thread ("overlap with " ++ (show t')) t'
                                                                   where
                                                                     access_overlaps (TraceLoad _ _ ptr' _) = ptr' == ptr
                                                                     access_overlaps (TraceStore _ _ ptr' _) = ptr' == ptr
                                                                     access_overlaps _ = False
                          in map (rc_access . trc_loc) racingAccesses
                      entry_for_thread t' =
                          case races_with_thread t' of
                            [] -> Nothing
                            (x:_) -> Just (x, t')
                      maybeEntries = map entry_for_thread $ filter ((/=) t) threads
                      deMaybe (Just x) y = x:y
                      deMaybe Nothing y = y
                  in foldr deMaybe [] maybeEntries
              thread_action t (acc, targ) =
                  setThread (fst $ runMemoryThread start t (acc + 1)) targ
              thread_actions = concat [map (thread_action t) (racing_access_for_thread t) | t <- threads]
              result = addEnumStates origin thread_actions trailer
          in result

{- Find all of the steps we can make which just advance us one
   racing access. -}
singleAccessAdvances :: History -> [History]
singleAccessAdvances start =
    let threads = live_threads start
        trace_for_thread t = traceThread start t
        footstep_is_mem (TraceLoad _ _ _ False) = True
        footstep_is_mem (TraceStore _ _ _ False) = True
        footstep_is_mem _ = False
        memtrace_for_thread' = filter (footstep_is_mem . trc_trc) . trace_for_thread
        thread_traces = zip threads $ map memtrace_for_thread' threads
        memtrace_for_thread t =
            case lookup t thread_traces of
              Just x -> x
              Nothing -> error $ "lost a thread somewhere, wanted " ++ (show t) ++ ", had " ++ (show thread_traces)
        racing_access_for_thread :: ThreadId -> [(AccessNr, ThreadId)]
        racing_access_for_thread t =
            let races_with_thread t' =
                    let racingAccesses =
                            filter (isRace . trc_trc) $ memtrace_for_thread t
                        isRace (TraceLoad _ _ ptr _) =
                            or $ map (isStore . trc_trc) $ overlapping_accesses ptr
                        isRace (TraceStore _ _ ptr _) =
                            case overlapping_accesses ptr of
                              [] -> False
                              _ -> True
                        isRace _ = False
                        isStore (TraceStore _ _ _ _) = True
                        isStore _ = False
                        overlapping_accesses ptr = filter (access_overlaps . trc_trc) $ memtrace_for_thread t'
                            where
                              access_overlaps (TraceLoad _ _ ptr' _) = ptr' == ptr
                              access_overlaps (TraceStore _ _ ptr' _) = ptr' == ptr
                              access_overlaps _ = False
                    in map (rc_access . trc_loc) racingAccesses
                entry_for_thread t' =
                    case races_with_thread t' of
                      [] -> Nothing
                      (x:_) -> Just (x, t')
                maybeEntries = map entry_for_thread $ filter ((/=) t) threads
                deMaybe (Just x) y = x:y
                deMaybe Nothing y = y
            in foldr deMaybe [] maybeEntries
        thread_action t (acc, targ) =
            setThread (fst $ runMemoryThread start t (acc + 1)) targ
        res = (concat [map (thread_action t) (racing_access_for_thread t) | t <- threads])
    in res

{- Given a small-step explorer, build an exhaustive big-step explorer -}
breadthFirstExplore :: (History -> [History]) -> History -> [History]
breadthFirstExplore step start =
    let addNextLevel [] = []
        addNextLevel previousLevel =
            previousLevel ++ (let nextLevel = concatMap step previousLevel
                              in addNextLevel nextLevel)
    in addNextLevel [start]

{- Find all of the paths we can take from this epoch to the very next
   one which don't cause an immediate failure. -}
{- We cheat a bit: if we find a path to the end of the entire log,
   we might just return that, rather than going through everything. -}
enumerateNextEpoch :: History -> [History]
enumerateNextEpoch start =
    dt ("enum epoch " ++ (show start)) $
    case replayState start of
      ReplayStateFinished _ -> [start]
      ReplayStateFailed _ _ _ _ -> []
      ReplayStateOkay start_coord ->
          let next_coord = Finite ReplayCoord { rc_access = rc_access start_coord + 5000}

              tweakedSchedules = breadthFirstExplore singleAccessAdvances start

              newSchedules = [deError $ run x next_coord | x <- tweakedSchedules]

              {- We filter the returned schedules so as we remove all
                 definitely-failed ones and get out quickly if we hit
                 the end of the replay log. -}
              {- The argument is likely to be very large and the result
                 will usually not be completely explored, so laziness
                 is important here. -}
              filterSchedules [] = []
              filterSchedules (x:xs) =
                  dt ("check schedule " ++ (show x)) $
                  case replayState x of
                    ReplayStateFinished _ -> [x]
                    ReplayStateOkay _ -> x:(filterSchedules xs)
                    ReplayStateFailed _ _ _ _ -> filterSchedules xs

              res = filterSchedules newSchedules
          in res

{- Enumerate big-step advances we can make in the history.  This
   means, basically, running the log as far as we can in
   trace-directed mode, and then backtracking one epoch at a time when
   we get a failure. -}
enumerateHistoriesBigStep :: History -> EnumerationState -> EnumerationState
enumerateHistoriesBigStep start trailer =
    case replayState start of
      ReplayStateFinished _ -> enumStateFinished start
      ReplayStateFailed _ _ _ _ -> trailer
      ReplayStateOkay start_epoch ->
          case replayState $ deError $ run start Infinity of
            ReplayStateFinished _ ->
                {- We're done; no point exploring any further -}
                enumStateFinished $ deError $ run start Infinity
            ReplayStateOkay _ -> error "replay got lost somewhere?"
            ReplayStateFailed _ _ fail_epoch _ ->
                tlog ("failed at " ++ (show fail_epoch)) $
                let epochs = map ReplayCoord [(rc_access start_epoch)..(rc_access fail_epoch)]
                    ss_starts = [if e == start_epoch
                                 then start 
                                 else deError $ run start (Finite e) | e <- epochs]
                in foldl (flip enumerateHistoriesSmallStep) trailer ss_starts

{- Exhaustively explore all future schedulings available from hist and
   return the first successful one (or Nothing, if we can't find
   anything. -}
enumerateHistories' :: EnumerationState -> Maybe History
enumerateHistories' startState =
    case getNextExploreState startState of
      Nothing -> Nothing -- failed
      Just (startHist, nextState) ->
          tlog ("explore " ++ (show startHist)) $
          case replayState startHist of
            ReplayStateFinished _ -> Just startHist -- Succeeded
            ReplayStateFailed _ _ _ _ -> enumerateHistories' nextState
            ReplayStateOkay _ -> enumerateHistories' $ enumerateHistoriesBigStep startHist nextState

enumerateHistories :: History -> Maybe History
--enumerateHistories start = enumerateHistories' $ EnumerationState [(startCoord, start)] emptyQueue start False
--enumerateHistories start = enumerateAllEpochs [start]
enumerateHistories start = case filter (\x -> case replayState x of
                                                ReplayStateFinished _ -> True
                                                _ -> False) $ breadthFirstExplore enumerateNextEpoch start of
                             [] -> Nothing
                             (x:_) -> Just x


{- For our current purposes, a racing expression is one in which a
   load in one thread is satisfied by a store in a different one. -}
isRacingExpression :: Expression -> Bool
isRacingExpression (ExpressionRegister _ _) = False
isRacingExpression (ExpressionConst _) = False
isRacingExpression (ExpressionLoad load_tid _ _ addr val) =
    (case val of
       ExpressionStore store_tid _ _ -> load_tid /= store_tid
       ExpressionImported _ -> False
       _ -> error "the value of a load should always be an import or a store") ||
              (isRacingExpression addr) ||
              (isRacingExpression val)
isRacingExpression (ExpressionStore _ _ e) = isRacingExpression e
isRacingExpression (ExpressionImported _) = False
isRacingExpression (ExpressionBinop _ a b) =
    isRacingExpression a || isRacingExpression b
isRacingExpression (ExpressionNot x) = isRacingExpression x

getRacingExpressions :: [Expression] -> [Expression]
getRacingExpressions = filter isRacingExpression


{- Go through and find all of the memory accesses in an expression,
   and then partition them into a bunch of critical sections.  A
   critical section, for our purposes, is a set of memory accesses
   which has to be executed atomically.  ``Atomic'' in this context is
   defined relative to all of the other critical sections in the list
   (so other accesses can be interleaved with these ones). -}
{- For now, we just create a critical section for every thread, and
   put all of its memory accesses into that section.  This is quite
   pessimistic, but easy to implement, and should at least work in
   most of the common cases. -}
criticalSections :: Expression -> [CriticalSection]
criticalSections expr =
    let accesses = foldrExpression
                   (ExpressionFolder
                    { ef_reg = const $ const [],
                      ef_const = const [],
                      ef_load = \tid _ when addr val -> (tid,when):(addr ++ val),
                      ef_store = \tid when val -> (tid,when):val,
                      ef_imported = const [],
                      ef_binop = \_ a b -> a ++ b,
                      ef_not = id })
                   expr
        threads = nub $ map fst accesses
        csForThread t = CriticalSection t [acc | (thr, acc) <- accesses, t == thr]
    in map csForThread threads

{- Look at a critical section and a history and figure out which RIPs
   should have been in the section.  All of the accesses in the CS
   have to be in the same thread for this to be correct. -}
getCriticalRips :: History -> CriticalSection -> [Word64]
getCriticalRips hist (CriticalSection interestingThread accesses) =
    let accesses' = sort accesses
        fstAccess = head accesses'
        
        accesses'' = tail $
                     filter
                     (\a -> nextThread (deError $ truncateHistory' hist $ Finite a) == interestingThread)
                     accesses'

        ripsInAccess :: ReplayCoord -> [Word64]
        ripsInAccess start@(ReplayCoord acc) =
            case trace (deError $ truncateHistory' hist $ Finite start) (Finite $ ReplayCoord $ acc + 1) of
              Left err -> error $ "ripsBetween: " ++ err
              Right (_, t) -> [rip | (TraceRecord (TraceFootstep rip _ _ _) _) <- t]

        {- We want to include the instruction which issued the first
           access.  Accesses terminate blocks, and the access shows up
           after the footstep in the log, so the footsteps won't
           include it, and so we need to grab it manually. -}
        fstRip = case getRipAtAccess hist fstAccess of
                   Left err -> error $ "ripsBetween2: " ++ err
                   Right v -> v
    in fstRip:(concatMap ripsInAccess accesses'')

data PatchFragment = PatchFragment { pf_literal :: [Word8],
                                     pf_fixups :: [PatchFixup] } deriving Show

data InstructionPrefixes = InstructionPrefixes { ip_rexw :: Bool,
                                                 ip_rexr :: Bool,
                                                 ip_rexx :: Bool,
                                                 ip_rexb :: Bool,
                                                 ip_lock :: Bool,
                                                 ip_repne :: Bool,
                                                 ip_repe :: Bool,
                                                 ip_cs :: Bool,
                                                 ip_ss :: Bool,
                                                 ip_ds :: Bool,
                                                 ip_es :: Bool,
                                                 ip_fs :: Bool,
                                                 ip_gs :: Bool,
                                                 ip_opsize :: Bool,
                                                 ip_addrsize :: Bool }

noInstrPrefixes :: InstructionPrefixes
noInstrPrefixes =
    InstructionPrefixes False False False False False False False
                        False False False False False False
                        False False

bytes :: History -> Word64 -> Word64 -> Either String [Word8]
bytes snapshot addr size =
    case fetchMemory snapshot addr size of
      Nothing -> Left $ "error fetching from " ++ (showHex addr "")
      Just x -> Right x

byte :: History -> Word64 -> Either String Word8
byte snapshot addr =
    do r <- bytes snapshot addr 1
       case r of
         [v] -> return v
         _ -> error "Huh? multiple bytes when we only asked for one"

stripPrefixes :: History -> Word64 -> Either String (Word64, InstructionPrefixes, [Word8])
stripPrefixes snapshot rip =
    do b <- byte snapshot rip
       case b of
         0x26 -> do (more_rip,more_prefixes,more_bytes) <- stripPrefixes snapshot (rip + 1)
                    return (more_rip,more_prefixes { ip_es = True }, b:more_bytes)
         0x2e -> do (more_rip,more_prefixes,more_bytes) <- stripPrefixes snapshot (rip + 1)
                    return (more_rip,more_prefixes { ip_cs = True }, b:more_bytes)
         0x36 -> do (more_rip,more_prefixes,more_bytes) <- stripPrefixes snapshot (rip + 1)
                    return (more_rip,more_prefixes { ip_ss = True }, b:more_bytes)
         0x3e -> do (more_rip,more_prefixes,more_bytes) <- stripPrefixes snapshot (rip + 1)
                    return (more_rip,more_prefixes { ip_ds = True }, b:more_bytes)
         0x64 -> do (more_rip,more_prefixes,more_bytes) <- stripPrefixes snapshot (rip + 1)
                    return (more_rip,more_prefixes { ip_fs = True }, b:more_bytes)
         0x65 -> do (more_rip,more_prefixes,more_bytes) <- stripPrefixes snapshot (rip + 1)
                    return (more_rip,more_prefixes { ip_gs = True }, b:more_bytes)
         0x66 -> do (more_rip,more_prefixes,more_bytes) <- stripPrefixes snapshot (rip + 1)
                    return (more_rip,more_prefixes { ip_opsize = True }, b:more_bytes)
         0x67 -> do (more_rip,more_prefixes,more_bytes) <- stripPrefixes snapshot (rip + 1)
                    return (more_rip,more_prefixes { ip_addrsize = True }, b:more_bytes)
         0xF0 -> do (more_rip,more_prefixes,more_bytes) <- stripPrefixes snapshot (rip + 1)
                    return (more_rip,more_prefixes { ip_lock = True }, b:more_bytes)
         0xf2 -> do (more_rip,more_prefixes,more_bytes) <- stripPrefixes snapshot (rip + 1)
                    return (more_rip,more_prefixes { ip_repne = True }, b:more_bytes)
         0xf3 -> do (more_rip,more_prefixes,more_bytes) <- stripPrefixes snapshot (rip + 1)
                    return (more_rip,more_prefixes { ip_repe = True }, b:more_bytes)
         _ -> if b >= 0x40 && b < 0x50
              then do (more_rip,more_prefixes,more_bytes) <- stripPrefixes snapshot (rip + 1)
                      return (more_rip,
                              more_prefixes { ip_rexw = b `testBit` 3,
                                              ip_rexr = b `testBit` 2,
                                              ip_rexx = b `testBit` 1,
                                              ip_rexb = b `testBit` 0 },
                              b:more_bytes)
              else return (rip, noInstrPrefixes, [])

bitSlice :: Bits a => a -> Int -> Int -> a
bitSlice val start end = (val `shiftR` start) .&. ((1 `shiftL` (end - start + 1)) - 1)

{- A patch fixup record means that the 4-byte value at offset pf_offset in the
   string should be modified to be pf_target - (pf_offset + pf_addend + address_of_string) -}
data PatchFixup = PatchFixup { pf_offset :: Word64,
                               pf_target :: Either String Word64,
                               pf_addend :: Word64 } deriving Show

offsetFixup :: Word64 -> PatchFixup -> PatchFixup
offsetFixup o p = p { pf_offset = o + pf_offset p }

byteListToInteger :: [Word8] -> Word64
byteListToInteger = foldr (\a b -> a + b * 256) 0 . map fromIntegral

{- Parse up a modrm sequence enough to discover:

   -- its length, including SIB and displacement if present.
   -- any fixups which might be necessary when we move it due to rip-relative addressing
 -}
parseModrm :: History -> InstructionPrefixes -> Word64 -> Word64 -> Word64 -> Either String (Word64, [Word8], [PatchFixup], Word8)
parseModrm snapshot _prefixes addr immediateBytes opcodeLen =
    do modrm <- byte snapshot addr
       let modfield = bitSlice modrm 6 7
           regfield = bitSlice modrm 3 5
           rmfield = bitSlice modrm 0 2
           useSib = rmfield == 4 && modfield /= 3
           modrmDispSize = case modfield of
                             0 -> if rmfield == 5
                                  then 4
                                  else 0
                             1 -> 1
                             2 -> 4
                             3 -> 0
                             _ -> error "bitSlice not working"
           ripRelative = rmfield == 5 && modfield == 0
       if useSib
        then do sib <- byte snapshot $ addr + 1
                let _sibScale = bitSlice sib 6 7
                    _sibIndex = bitSlice sib 3 5
                    sibBase = bitSlice sib 0 2
                    sibDispSize = if sibBase == 5
                                  then case modfield of
                                         0 -> 4
                                         1 -> 1
                                         2 -> 4
                                         _ -> error "bitSlice not working"
                                  else 0
                if dt ("have sib " ++ (showHex sib "")) $ sibDispSize /= 0 && modrmDispSize /= 0 && sibDispSize /= modrmDispSize
                 then Left $ "bad modrm decode at " ++ (showHex addr "") ++ ": modrm disp size doesn't match SIB disp size"
                 else let dispSize = if sibDispSize /= 0
                                     then sibDispSize
                                     else modrmDispSize
                      in do dispBytes <- bytes snapshot (addr + 2) dispSize
                            return (addr + 2 + dispSize, modrm:sib:dispBytes,
                                    if ripRelative
                                    then [PatchFixup (opcodeLen + 2) (Right $ addr + 2 + immediateBytes + dispSize + byteListToInteger dispBytes) (immediateBytes + dispSize)]
                                    else [],
                                    regfield)
        else do dispBytes <- bytes snapshot (addr + 1) modrmDispSize
                return (addr + 1 + modrmDispSize, modrm:dispBytes,
                        if ripRelative
                        then [PatchFixup (opcodeLen + 1) (Right $ addr + 1 + immediateBytes + modrmDispSize + byteListToInteger dispBytes) (immediateBytes + modrmDispSize)]
                        else [],
                        regfield)

{- Concatenate two patch fragments -}
prefixPatchFragment :: PatchFragment -> PatchFragment -> PatchFragment
prefixPatchFragment fstFrag sndFrag =
    PatchFragment { pf_literal = pf_literal fstFrag ++ pf_literal sndFrag,
                    pf_fixups = pf_fixups fstFrag ++ (map (offsetFixup $ fromIntegral $ length $ pf_literal fstFrag) $ pf_fixups sndFrag) }

ripListToPatchFragment :: History -> [Word64] -> PatchFragment -> Either String (PatchFragment, Word64)
ripListToPatchFragment _ [] _ = error "ripListToPatchFragment on empty"
ripListToPatchFragment snapshot (rip:rips) end =
    do (after_prefix_rip, prefixes, prefix_string) <- stripPrefixes snapshot rip
       hbyte <- byte snapshot after_prefix_rip
       let opcodeLen = after_prefix_rip + 1 - rip
           justModrm :: Either String (PatchFragment, Word64)
           justModrm =
               do (nrip, modrm_bytes, modrm_fixups, _) <- parseModrm snapshot prefixes (after_prefix_rip + 1) 0 opcodeLen
                  let myPF = PatchFragment { pf_literal = prefix_string ++ [hbyte] ++ modrm_bytes,
                                             pf_fixups = modrm_fixups}
                   in case rips of
                       [] -> return (prefixPatchFragment myPF end, nrip)
                       _ -> do (restPf, finalRip) <- ripListToPatchFragment snapshot rips end
                               return (prefixPatchFragment myPF restPf, finalRip)
       case hbyte of
         0x83 -> do (after_modrm_rip, modrm_bytes, modrm_fixups, extension) <- parseModrm snapshot prefixes (after_prefix_rip + 1) 1 opcodeLen
                    case extension of
                      0 -> do imm8 <- byte snapshot after_modrm_rip
                              let myPF = PatchFragment { pf_literal = prefix_string ++ [hbyte] ++ modrm_bytes ++ [imm8],
                                                         pf_fixups = modrm_fixups}
                               in case rips of
                                    [] -> return (prefixPatchFragment myPF end, after_modrm_rip)
                                    _ -> do (restPf, finalRip) <- ripListToPatchFragment snapshot rips end
                                            return (prefixPatchFragment myPF restPf, finalRip)
                      _ -> Left $ "unknown instruction 0x83 extension at " ++ (showHex rip "")
         0x89 -> justModrm
         0x8b -> justModrm
         _ -> Left $ "unknown instruction at " ++ (showHex rip "")

byteListToCString :: [Word8] -> String
byteListToCString bl = '"':(concatMap word8ToCChar bl) ++ "\""
                       where word8ToCChar x = "\\x" ++ (showHex x "")

fixupToC :: String -> PatchFixup -> String
fixupToC pattern_ident pf =
    let targ = case pf_target pf of
                 Left s -> "(unsigned long)" ++ s
                 Right i -> "0x" ++ (showHex i "")
    in pattern_ident ++ "[" ++ (show $ pf_offset pf) ++ "] = " ++ targ ++ " - (" ++ (show $ pf_offset pf) ++ " + " ++ (show $ pf_addend pf) ++ " + (unsigned long)" ++ pattern_ident ++ ");\n"

callSymbolFragment :: String -> PatchFragment
callSymbolFragment symb = PatchFragment { pf_literal = [0x48, 0x81, 0xec, 0x80, 0x00, 0x00, 0x00, {- subq $128, %rsp -> get out of the red zone -}
                                                        0xe8, 0x00, 0x00, 0x00, 0x00, {- call disp32 -}
                                                        0x48, 0x81, 0xc4, 0x80, 0x00, 0x00, 0x00 {- addq $128, %rsp -}],
                                          pf_fixups = [PatchFixup { pf_offset = 8, pf_target = Left symb, pf_addend = 4 }]}

jmpAddressFragment :: Word64 -> PatchFragment
jmpAddressFragment targ = PatchFragment { pf_literal = [0xe9, 0x00, 0x00, 0x00, 0x00 {- jmp disp32 -}],
                                          pf_fixups = [PatchFixup { pf_offset = 1, pf_target = Right targ, pf_addend = 4 }]}

mkFixup :: History -> CriticalSection -> [String] -> Either String (String, String, [String])
mkFixup hist cs (pattern_ident:identifiers) =
    let crit_rips = getCriticalRips hist cs in
    mdo
       (patch_frag, nextRip) <- ripListToPatchFragment hist crit_rips $ prefixPatchFragment (callSymbolFragment "do_unlock") (jmpAddressFragment nextRip)
       let patch_frag' = prefixPatchFragment (callSymbolFragment "do_lock") patch_frag
           pattern = byteListToCString $ pf_literal patch_frag'
           global_part = "static unsigned char *" ++ pattern_ident ++ " = " ++ pattern ++ ";\n" ++
                         "static unsigned char *" ++ pattern_ident ++ " __attribute__ ((\"read_write_exec\"));\n" ++
                         "REGISTER_FIXUP(0x" ++ (showHex (head crit_rips) "") ++ ", " ++ pattern_ident ++ ");\n"
           local_part = foldr (++) "" $ map (fixupToC pattern_ident) $ pf_fixups patch_frag'
       return $  (local_part, global_part, identifiers)

mkFixups :: History -> [CriticalSection] -> [String] -> Either String [(String, String)]
mkFixups _ [] _ = Right []
mkFixups hist (cs:css) idents =
    do (a, b, idents') <- mkFixup hist cs idents
       rest <- mkFixups hist css idents'
       return $ (a,b):rest

mkFixupLibrary :: History -> [CriticalSection] -> Either String String
mkFixupLibrary hist crit_sects =
    do fixups <- mkFixups hist crit_sects ["id_" ++ (show x) | x <- [(0::Integer)..]]
       let (local, global) = foldr (\(a, b) (c, d) -> (a:c, b:d)) ([], []) fixups
           res = "#include \"fixup_lib_const.h\"\n" ++ (concat global) ++ "void _entry(void) {\n" ++ (concat local) ++ "activate_fixups();\n}"
       return res
