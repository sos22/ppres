module Analysis(findRacingAccesses, findControlFlowRaces, 
                evalExpressionInSnapshot, evalExpressionWithStore,
                enumerateHistories) where

import Types
import WorkerCache
import History
import ReplayState()
import Timing

import Data.Bits
import Data.Word
import Data.List

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
    dt ("trace thread " ++ (show thr) ++ " in " ++ (show start)) $
    case histCoord start of
      Infinity -> []
      Finite cur_record ->
          let new_record = ReplayCoord { rc_access = rc_access cur_record + 50000 }
          in snd $ trace (appendHistory start $ HistorySetThread thr) $ Finite new_record

runMemoryThread :: History -> ThreadId -> AccessNr -> (History, [TraceRecord])
runMemoryThread start tid acc =
    let targetCoord = ReplayCoord acc
    in trace (appendHistory start (HistorySetThread tid)) $ Finite targetCoord

fetchMemory8 :: History -> Word64 -> Maybe Word64
fetchMemory8 hist addr =
    do bytes <- fetchMemory hist addr 8
       return $ fromInteger $ foldr (\a b -> b * 256 + a) 0 $ map toInteger bytes

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
              trivHistory = run start next_coord

              tweakedSchedules = breadthFirstExplore singleAccessAdvances start

              newSchedules = [run x next_coord | x <- tweakedSchedules]

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

enumerateAllEpochs :: [History] -> Maybe History
enumerateAllEpochs [] = Nothing
enumerateAllEpochs [x] =
    case replayState x of
      ReplayStateFinished _ -> Just x
      _ -> enumerateAllEpochs $ enumerateNextEpoch x
enumerateAllEpochs (thisHist:otherHists) =
    dt ("enum big " ++ (show thisHist)) $
    enumerateAllEpochs $ (enumerateNextEpoch thisHist) ++ otherHists

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
          case replayState $ run start Infinity of
            ReplayStateFinished _ ->
                {- We're done; no point exploring any further -}
                enumStateFinished $ run start Infinity
            ReplayStateOkay _ -> error "replay got lost somewhere?"
            ReplayStateFailed _ _ fail_epoch _ ->
                tlog ("failed at " ++ (show fail_epoch)) $
                let epochs = map ReplayCoord [(rc_access start_epoch)..(rc_access fail_epoch)]
                    ss_starts = [if e == start_epoch
                                 then start 
                                 else run start (Finite e) | e <- epochs]
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

