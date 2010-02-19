module Analysis(findRacingAccesses, findControlFlowRaces, fixControlHistory,
                fixControlHistory', findCritPairs, flipPair, advanceHist,
                enumerateHistories) where

import Types
import WorkerCache
import History
import ReplayState()
import Timing

import qualified Debug.Trace
import Data.Bits
import Data.Word
import Data.List

dt :: String -> b -> b
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
                                     (ExpressionMem _ loc2 _ _) = loc1 == loc2
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
evalExpressionWithStore (ExpressionMem _ _ addr val) st =
    do addr' <- evalExpressionWithStore addr st
       val' <- evalExpressionWithStore val st
       return $ case lookup addr' st of
                  Nothing -> val'
                  Just v -> v
evalExpressionWithStore (ExpressionImported v) _ = Just v
evalExpressionWithStore (ExpressionNot e) st =
    fmap complement $ evalExpressionWithStore e st
evalExpressionWithStore (ExpressionBinop BinopCombine _ _) _ = Nothing
evalExpressionWithStore (ExpressionBinop op l' r') st =
    do l <- evalExpressionWithStore l' st
       r <- evalExpressionWithStore r' st
       return $ binopFunc op l r

live_threads :: History -> [ThreadId]
live_threads _ = [1,2]

traceThread :: History -> ThreadId -> [TraceRecord]
traceThread start thr =
    let cur_record = case replayState start of
                       ReplayStateOkay x -> Finite x
                       ReplayStateFinished -> Infinity
                       ReplayStateFailed _ _ _ e _ -> Finite e
    in snd $ trace (appendHistory start $ HistorySetThread thr) (cur_record + 1)

runMemoryThread :: History -> ThreadId -> Integer -> (History, [TraceRecord])
runMemoryThread start tid cntr =
    runMemory (appendHistory start (HistorySetThread tid)) cntr

fixControlHistoryL :: History -> [[History]]
fixControlHistoryL start =
    let (ReplayStateFailed _ _ dead_thread epoch_nr _) = replayState start
        probes_order_n n =
            let prefix = truncateHistory start $ Finite $ epoch_nr - n
                criticalExpressions = [(e, evalExpressionWithStore e []) | e <- controlTrace prefix Infinity]
                otherThreads = [x | x <- live_threads start, x /= dead_thread]
                otherStoresForThread t =
                    [(ptr, val, when) | (TraceRecord (TraceStore val _ ptr _ ) when) <- traceThread prefix t]
                storeSatisfiesExpression (ptr,val,_) (expr, v) =
                    evalExpressionWithStore expr [(ptr,val)] /= v
                satisfiedExpressions st =
                    [ind | (ind, expr) <- zip [0..] criticalExpressions, storeSatisfiesExpression st expr]
                interestingStores =
                    concat [[(st, ind) | st <- otherStoresForThread t, ind <- satisfiedExpressions st]
                            | t <- otherThreads]
                tryStore ((_, _, (TraceLocation _ _ acc thr)), _) =
                    run (fst $ runMemoryThread prefix thr (acc + 1)) Infinity
            in map tryStore interestingStores
        allProbes = map probes_order_n [1..32]
    in allProbes

{- One of the strategies for fixing replays which don't work.  Back up
   to the previous non-failing record, then do a control trace forward
   in the failing thread.  That'll give us a bunch of expressions such
   that making any of them true will cause the replay to behave
   differently.  Once we've got them, we do a tracet on the other
   threads in the replay, and see if they have any writes which would
   cause an expression to become true.  If they do, we try running
   those accesses before running the failed thread.  If that succeeds,
   we return the resulting history. -}
fixControlHistory' :: History -> Maybe History
fixControlHistory' start =
    case replayState start of
      ReplayStateOkay _ -> Nothing
      ReplayStateFinished -> Nothing
      ReplayStateFailed _ _ _ nr_epochs _ ->
          let probes = head $ fixControlHistoryL start
              allProbes = [(p, replayState p) | p <- probes]
              probeIsGood (_, ReplayStateOkay _) = True
              probeIsGood (_, ReplayStateFinished) = True
              probeIsGood (_, ReplayStateFailed _ _ _ progress _ ) =
                  progress > nr_epochs
              goodProbes = filter probeIsGood allProbes
              probeIsVeryGood (_, ReplayStateOkay _) = True
              probeIsVeryGood (_, ReplayStateFinished) = True
              probeIsVeryGood (_, ReplayStateFailed _ _ _ progress _) =
                  progress > nr_epochs + 100
              compareFailureReasons ReplayStateFinished _ = LT
              compareFailureReasons (ReplayStateOkay _) _ = LT
              compareFailureReasons _ (ReplayStateOkay _) = GT
              compareFailureReasons _ ReplayStateFinished = GT
              compareFailureReasons (ReplayStateFailed _ proga _ _ _)
                                    (ReplayStateFailed _ progb _ _ _) =
                                        compare proga progb
              sortedProbes = sortBy ordering goodProbes
                             where ordering (_, ra) (_, rb) = compareFailureReasons ra rb
          in dt ("probes " ++ (show allProbes)) $
             dt ("sortedProbes " ++ (show sortedProbes)) $
             case find probeIsVeryGood goodProbes of
               Just (x, _) -> Just x
               Nothing ->
                   case sortedProbes of
                     [] -> Nothing
                     ((x,_):_) -> Just x

fixControlHistory :: History -> History
fixControlHistory start =
    case fixControlHistory' start of
      Nothing -> start
      Just x -> fixControlHistory x

fetchMemory8 :: History -> Word64 -> Maybe Word64
fetchMemory8 hist addr =
    do bytes <- fetchMemory hist addr 8
       return $ fromInteger $ foldr (\a b -> b * 256 + a) 0 $ map toInteger bytes

evalExpressionInSnapshot :: Expression -> History -> [(Word64, Word64)] -> Maybe Word64
evalExpressionInSnapshot (ExpressionRegister _ n) _ _ = Just n
evalExpressionInSnapshot (ExpressionConst n) _ _ = Just n
evalExpressionInSnapshot (ExpressionMem _ _ addr _) hist stores =
    do addr' <- evalExpressionInSnapshot addr hist stores
       case lookup addr' stores of
         Nothing -> fetchMemory8 hist addr'
         Just v -> Just v
evalExpressionInSnapshot (ExpressionImported v) _ _ = Just v
evalExpressionInSnapshot (ExpressionBinop BinopCombine _ _) _ _ = Nothing
evalExpressionInSnapshot (ExpressionBinop op l' r') hist st =
    do l <- evalExpressionInSnapshot l' hist  st
       r <- evalExpressionInSnapshot r' hist st
       return $ binopFunc op l r
evalExpressionInSnapshot (ExpressionNot l) hist st =
    fmap complement $ evalExpressionInSnapshot l hist st

lastSucceedingRecordAnyThread :: History -> (ThreadId, EpochNr)
lastSucceedingRecordAnyThread hist =
    let myMax a b = if ts_last_epoch (snd a) <= ts_last_epoch (snd b)
                    then b
                    else a
        (tid, ts) = foldl1 myMax $ threadState hist
    in (tid, ts_last_epoch ts)

threadState' :: History -> ThreadId -> ThreadState
threadState' hist thr =
    case lookup thr $ threadState hist of
      Nothing -> error "lost a thread"
      Just ts -> ts

{- This is trying to fix races assuming that we've just transitioned
   from thread A to thread B and then failed in the first record of
   thread B.  We try to fix it by moving some of the thread B accesses
   a little bit earlier, so that they overlap with the last thread A
   record. -}
findCritPairs :: History -> [(TraceLocation, TraceLocation)]
findCritPairs hist =
    case replayState hist of
      ReplayStateOkay _ -> []
      ReplayStateFinished -> []
      ReplayStateFailed _ _ threadB _ _ ->
          let (threadA, threadALastSuccess) = lastSucceedingRecordAnyThread hist
              prefix1 = truncateHistory hist $ Finite $ threadALastSuccess
              prefix2 = truncateHistory hist $ Finite $ (ts_last_epoch $ threadState' hist threadA) - 1
              ctrl_expressions = controlTrace prefix1 Infinity
              store_trace = [(ptr, val, when) | (TraceRecord (TraceStore val _ ptr _) when) <- snd $ trace prefix2 $ Finite threadALastSuccess]
              store_changes_expr expr (ptr, val, _) =
                  evalExpressionInSnapshot expr prefix2 [] /= evalExpressionInSnapshot expr prefix2 [(ptr, val)]
              expressionLocations p@(ptr, _, _) expr =
                  case expr of
                    ExpressionRegister _ _ -> []
                    ExpressionConst _ -> []
                    ExpressionMem _ loc ptr' _ ->
                        (case evalExpressionInSnapshot ptr' prefix2 [] of
                           Just ptr'' | ptr'' == ptr ->
                                         ((:) loc)
                           _ -> id) $ expressionLocations p ptr'
                    ExpressionImported _ -> []
                    ExpressionBinop _ l r -> (expressionLocations p l) ++ (expressionLocations p r)
                    ExpressionNot x -> expressionLocations p x
              critical_pairs = [(st, exprloc) | expr <- ctrl_expressions,
                                                st <- store_trace,
                                                exprloc <- expressionLocations st expr,
                                                store_changes_expr expr st]
          in dt ("threadA " ++ (show threadA)) $
             dt ("threadB " ++ (show threadB)) $
             dt ("last success " ++ (show threadALastSuccess)) $
             if threadA == threadB
             then []
             else [(l, e) | ((_, _, l), e) <- critical_pairs]


{- flipPair hist (acc1, acc2) -> tweak hist so that it runs up to the
   record before acc1, then runs acc1's thread until the access
   immediately before acc1, then run acc2's thread until the access
   immediately after acc2.  If acc2 is an access shortly after acc1
   then this has the effect or reordering them so that acc2 happens
   immediately before acc1. -}
{- This really only makes sense if the acc2's thread is actually
   runnable and if acc2 is in the next record which it has to run.  It
   pretty much means to flip one of the races found by
   findCritPairs. -}
flipPair :: History -> (TraceLocation, TraceLocation) -> History
flipPair start (post, pre) =
    let (prefix, trc) =
            runMemoryThread (truncateHistory start $ Finite $ trc_epoch post)
                                (trc_thread post) (trc_access post)
        (res, trc2) =
            runMemoryThread prefix (trc_thread pre) (trc_access pre + 1)
    in dt ("flipPair " ++ (show post) ++ " " ++ (show pre)) $
       dt ("trc1 " ++ (show trc)) $
       dt ("trc2 " ++ (show trc2)) $
       res

type Goodness a = a -> Topped Integer
type Explorer a = a -> [[a]]

historyGoodness :: Goodness History
historyGoodness hist =
    case replayState hist of
      ReplayStateOkay _ -> Infinity
      ReplayStateFinished -> Infinity
      ReplayStateFailed _ (RecordNr x) _ _ _ -> Finite x

data ExplorationParameters a = ExplorationParameters { ep_advance :: Explorer a,
                                                       ep_goodness :: Goodness a}

{- The idea is that we maintain a list of things which we're currently
   investigating, known as the fringe, and another list of points
   which we could sensibly backtrack to.  The main difference between
   fringe and backtrack is that a backtrack point is somewhat more
   expensive to visit, and so we don't want to go there unless the
   fringe is empty. -}
data Show a => ExplorationState a = ExplorationState { es_fringe :: [(Topped Integer, a)],
                                                       es_backtracks :: [[a]] } deriving Show

exploreStep :: Show a => ExplorationParameters a -> ExplorationState a -> Maybe ((Topped Integer, a), ExplorationState a)
exploreStep params state =
    case es_fringe state of
      [] ->
          case es_backtracks state of
            [] -> Nothing
            (x:xs) ->
                exploreStep params $ ExplorationState { es_fringe = [(ep_goodness params x', x') | x' <- x],
                                                        es_backtracks = xs }
      (s@(_, startingPoint):otherFringe) ->
          case ep_advance params startingPoint of
            [] -> exploreStep params $ state { es_fringe = otherFringe }
            (newFringePoints:newBacktrackPoints) ->
                let newItems = [(ep_goodness params x, x) | x <- newFringePoints]
                    newFringe = sortBy (\a b -> (fst a) `compare` (fst b)) $ newItems ++ otherFringe
                    newBacktrack = newBacktrackPoints ++ (es_backtracks state)
                in case newFringe of
                     [] -> exploreStep params $ state { es_fringe = [] }
                     ((bestGoodness,_):_) ->
                                  Just (s, ExplorationState { es_fringe = filter (\x -> fst x > bestGoodness - 1000) newFringe,
                                                              es_backtracks = newBacktrack })
               
explore :: Show a => ExplorationParameters a -> ExplorationState a -> Maybe a
explore params state =
    case exploreStep params state of
      Nothing -> Nothing
      Just (start, state') ->
          worker start state'
          where worker (Infinity,x) _ = Just x
                worker (thisGoodness, this) st =
                    case exploreStep params st of
                      Nothing -> Just this
                      Just ((newGoodness, newThing),st') ->
                          worker (if newGoodness > thisGoodness
                                  then (newGoodness, newThing)
                                  else (thisGoodness, this)) st'

advanceHist :: History -> History
advanceHist hist =
    case explore (ExplorationParameters { ep_goodness = historyGoodness,
                                          ep_advance = fixControlHistoryL })
                 (ExplorationState { es_fringe = [],
                                     es_backtracks = [[hist]] }) of
      Nothing -> hist
      Just h -> h

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

rs_epoch :: ReplayState -> Topped EpochNr
rs_epoch (ReplayStateOkay x) = Finite x
rs_epoch (ReplayStateFinished) = Infinity
rs_epoch (ReplayStateFailed _ _ _ e _) = Finite e

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
data EnumerationState = EnumerationState {ens_stack :: [History],
                                          ens_queue :: Queue History,
                                          ens_current :: History }

addEnumState :: History -> EnumerationState -> EnumerationState
addEnumState new es =
    let currentEpoch = rs_epoch $ replayState $ ens_current es
        newEpoch = rs_epoch $ replayState new
        flushQueue = newEpoch > currentEpoch - 10
        new_stack = if flushQueue
                    then queueToList (ens_queue es) (ens_stack es)
                    else ens_stack es
        new_queue = if flushQueue
                    then singletonQueue new
                    else appendQueue new $ ens_queue es
    in es { ens_stack = new_stack,
            ens_queue = new_queue }

addEnumStates :: [History] -> EnumerationState -> EnumerationState
addEnumStates xs es = foldr addEnumState es xs

enumStateFinished :: History -> EnumerationState
enumStateFinished hist = EnumerationState {ens_stack = [hist],
                                           ens_queue = emptyQueue,
                                           ens_current = hist}

getNextExploreState :: EnumerationState -> Maybe (History, EnumerationState)
getNextExploreState es =
    case queuePop $ ens_queue es of
      Nothing ->
          case ens_stack es of
            [] -> Nothing
            (a:as) -> Just (a, es { ens_stack = as })
      Just (a, new_queue) ->
          Just (a, es {ens_queue = new_queue})

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
      ReplayStateFailed _ _ _ _ _ -> trailer
      ReplayStateFinished -> enumStateFinished start
      ReplayStateOkay _ ->
          let threads = [a | (a, b) <- threadState start, not (ts_dead b || ts_blocked b) ]
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

              racing_access_for_thread :: ThreadId -> [(Integer, ThreadId)]
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
                          in map (trc_access . trc_loc) racingAccesses
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
              result = addEnumStates thread_actions trailer
          in result

{- Enumerate big-step advances we can make in the history.  This
   means, basically, running the log as far as we can in
   trace-directed mode, and then backtracking one epoch at a time when
   we get a failure. -}
enumerateHistoriesBigStep :: History -> EnumerationState -> EnumerationState
enumerateHistoriesBigStep start trailer =
    case replayState start of
      ReplayStateFinished -> enumStateFinished start
      ReplayStateFailed _ _ _ _ _ -> trailer
      ReplayStateOkay start_epoch ->
          case replayState $ run start Infinity of
            ReplayStateFinished ->
                {- We're done; no point exploring any further -}
                enumStateFinished $ run start Infinity
            ReplayStateOkay _ -> error "replay got lost somewhere?"
            ReplayStateFailed _ _ _ fail_epoch _ ->
                tlog ("failed at " ++ (show fail_epoch)) $
                let ss_starts = [if e == start_epoch
                                 then start 
                                 else run start (Finite e) | e <- reverse [start_epoch..fail_epoch]]
                in foldr enumerateHistoriesSmallStep trailer ss_starts

{- Exhaustively explore all future schedulings available from hist and
   return the first successful one (or Nothing, if we can't find
   anything. -}
enumerateHistories' :: EnumerationState -> Maybe History
enumerateHistories' startState =
    case getNextExploreState startState of
      Nothing -> Nothing -- failed
      Just (startHist, nextState) ->
          case replayState startHist of
            ReplayStateFinished -> Just startHist -- Succeeded
            ReplayStateFailed _ _ _ _ _ -> enumerateHistories' nextState
            ReplayStateOkay _ -> enumerateHistories' $ enumerateHistoriesBigStep startHist nextState

enumerateHistories :: History -> Maybe History
enumerateHistories start = enumerateHistories' $ EnumerationState [start] emptyQueue start
