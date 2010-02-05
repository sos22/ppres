module Analysis(findRacingAccesses, findControlFlowRaces, fixControlHistory,
                fixControlHistory', findCritPairs, flipPair, advanceHist,
                enumerateHistories) where

import Types
import WorkerCache
import Expression()
import History
import ReplayState()

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

fixControlHistoryL :: History -> [[History]]
fixControlHistoryL start =
    let (ReplayStateFailed _ (FailureReasonControl _ dead_thread epoch_nr)) = replayState start
        probes_order_n n =
            let prefix = truncateHistory start $ Finite $ epoch_nr - n
                criticalExpressions = [(e, evalExpressionWithStore e []) | e <- controlTrace prefix Infinity]
                otherThreads = [x | x <- live_threads start, x /= dead_thread]
                otherStoresForThread t =
                    [(ptr, val, when) | (TraceRecord (TraceStore val _ ptr _ ) when) <- snd $ traceThread prefix t]
                storeSatisfiesExpression (ptr,val,_) (expr, v) =
                    evalExpressionWithStore expr [(ptr,val)] /= v
                satisfiedExpressions st =
                    [ind | (ind, expr) <- zip [0..] criticalExpressions, storeSatisfiesExpression st expr]
                interestingStores =
                    concat [[(st, ind) | st <- otherStoresForThread t, ind <- satisfiedExpressions st]
                            | t <- otherThreads]
                tryStore ((_, _, (TraceLocation _ _ acc thr)), _) =
                    run (fst $ runMemory prefix thr (acc + 1)) Infinity
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
      ReplayStateFailed _ (FailureReasonControl _ _ nr_epochs) ->
          let probes = head $ fixControlHistoryL start
              allProbes = [(p, replayState p) | p <- probes]
              probeIsGood (_, ReplayStateOkay _) = True
              probeIsGood (_, ReplayStateFinished) = True
              probeIsGood (_, ReplayStateFailed _ (FailureReasonControl _ _ progress)) =
                  progress > nr_epochs
              goodProbes = filter probeIsGood allProbes
              probeIsVeryGood (_, ReplayStateOkay _) = True
              probeIsVeryGood (_, ReplayStateFinished) = True
              probeIsVeryGood (_, ReplayStateFailed _ (FailureReasonControl _ _ progress)) =
                  progress > nr_epochs + 100
              compareFailureReasons ReplayStateFinished _ = LT
              compareFailureReasons (ReplayStateOkay _) _ = LT
              compareFailureReasons _ (ReplayStateOkay _) = GT
              compareFailureReasons _ ReplayStateFinished = GT
              compareFailureReasons (ReplayStateFailed _ (FailureReasonControl proga _ _))
                                    (ReplayStateFailed _ (FailureReasonControl progb _ _)) =
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
      ReplayStateFailed _ (FailureReasonControl _ threadB _) ->
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
            runMemory (truncateHistory start $ Finite $ trc_epoch post)
                          (trc_thread post) (trc_access post)
        (res, trc2) =
            runMemory prefix (trc_thread pre) (trc_access pre + 1)
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
      ReplayStateFailed _ (FailureReasonControl (RecordNr x) _ _) -> Finite x

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
enumerateHistoriesSmallStep :: History -> [History] -> [History]
enumerateHistoriesSmallStep start trailer =
    case replayState start of
      ReplayStateFailed _ _ -> trailer
      ReplayStateFinished -> [start]
      ReplayStateOkay _ ->
          let threads = [a | (a, b) <- threadState start, not (ts_dead b || ts_blocked b) ]
              trace_for_thread t = snd $ traceThread start t
              footstep_is_mem (TraceLoad _ _ _ False) = True
              footstep_is_mem (TraceStore _ _ _ False) = True
              footstep_is_mem _ = False
              memtrace_for_thread' = filter footstep_is_mem . map trc_trc . trace_for_thread
              thread_traces = zip threads $ map memtrace_for_thread' threads
              memtrace_for_thread t =
                  case lookup t thread_traces of
                    Just x -> x
                    Nothing -> error "lost a thread somewhere"

              {- The index of the first racing access in a given
                 thread, or Nothing if there are no races in that
                 thread. -}
              racing_access_for_thread :: ThreadId -> Maybe Integer
              racing_access_for_thread t =
                  let access_races i =
                          let overlapping_accesses ptr =
                                  [x | t' <- threads, t' /= t, x <- memtrace_for_thread t', access_overlaps x]
                                  where access_overlaps (TraceLoad _ _ ptr' _) = ptr' == ptr
                                        access_overlaps (TraceStore _ _ ptr' _) = ptr' == ptr
                                        access_overlaps _ = False
                          in case (memtrace_for_thread t)!!i of
                               (TraceLoad _ _ ptr _) ->
                                   or $ map isStore $ overlapping_accesses ptr
                                   where isStore (TraceStore _ _ _ _) = True
                                         isStore _ = False
                               (TraceStore _ _ ptr _) ->
                                   or $ map (const True) $ overlapping_accesses ptr
                               _ -> error "strange kind of memory trace record"
                  in fmap (toInteger  . (1 + )) $ elemIndex True $ map access_races [0..((length $ memtrace_for_thread t)-1)]
              thread_action t =
                  case racing_access_for_thread t of
                    Just i -> Just $ fst $ runMemory start t i
                    Nothing -> Nothing
              thread_actions = map thread_action threads
              result =
                  foldr deMaybe trailer thread_actions
                  where deMaybe (Just x) y = x:y
                        deMaybe Nothing y = y
          in result

{- Enumerate big-step advances we can make in the history.  This
   means, basically, running the log as far as we can in
   trace-directed mode, and then backtracking one epoch at a time when
   we get a failure. -}
enumerateHistoriesBigStep :: History -> [History] -> [History]
enumerateHistoriesBigStep start trailer =
    case replayState start of
      ReplayStateFinished -> [start]
      ReplayStateFailed _ _ -> trailer
      ReplayStateOkay start_epoch ->
          case replayState $ run start Infinity of
            ReplayStateFinished ->
                {- We're done; no point exploring any further -}
                [run start Infinity]
            ReplayStateOkay _ -> error "replay got lost somewhere?"
            ReplayStateFailed _ (FailureReasonControl _ _ fail_epoch) ->
                let ss_starts = [if e == start_epoch
                                 then start 
                                 else run start (Finite e) | e <- reverse [start_epoch..fail_epoch]]
                in foldr enumerateHistoriesSmallStep trailer ss_starts

{- Exhaustively explore all future schedulings available from hist and
   return the first successful one (or Nothing, if we can't find
   anything. -}
enumerateHistories :: [History] -> Maybe History
enumerateHistories [] = Nothing
enumerateHistories (a:as) =
    dt ("explore " ++ (show a)) $
    case replayState a of
      ReplayStateFinished -> Just a -- We're done
      ReplayStateFailed _ _ -> enumerateHistories as -- Strip off any which have already failed
      ReplayStateOkay _ -> -- we have to do something more clever
          enumerateHistories $ enumerateHistoriesBigStep a as
