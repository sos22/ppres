module Analysis(findRacingAccesses, findControlFlowRaces, fixControlHistory,
                fixControlHistory', findCritPairs, flipPair, advanceHist) where

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

fixControlHistoryL :: History -> [History]
fixControlHistoryL start =
    let (ReplayStateFailed _ (FailureReasonControl record_nr dead_thread)) = replayState start
        prefix = truncateHistory start $ Finite record_nr
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
        tryStore ((_, _, (TraceLocation _ acc thr)), _) =
            run (fst $ runMemory prefix thr (acc + 1)) Infinity
        allProbes = map tryStore interestingStores
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
      ReplayStateOkay -> Nothing
      ReplayStateFinished -> Nothing
      ReplayStateFailed _ (FailureReasonControl nr_records _) ->
          let probes = fixControlHistoryL start
              allProbes = [(p, replayState p) | p <- probes]
              probeIsGood (_, ReplayStateOkay) = True
              probeIsGood (_, ReplayStateFinished) = True
              probeIsGood (_, ReplayStateFailed _ (FailureReasonControl progress _)) =
                  progress > nr_records
              goodProbes = filter probeIsGood allProbes
              probeIsVeryGood (_, ReplayStateOkay) = True
              probeIsVeryGood (_, ReplayStateFinished) = True
              probeIsVeryGood (_, ReplayStateFailed _ (FailureReasonControl (RecordNr progress) _)) =
                  let (RecordNr n) = nr_records
                  in progress > n + 10000
              compareFailureReasons ReplayStateFinished _ = LT
              compareFailureReasons ReplayStateOkay _ = LT
              compareFailureReasons _ ReplayStateOkay = GT
              compareFailureReasons _ ReplayStateFinished = GT
              compareFailureReasons (ReplayStateFailed _ (FailureReasonControl proga _))
                                    (ReplayStateFailed _ (FailureReasonControl progb _)) =
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

lastSucceedingRecordAnyThread :: History -> (ThreadId, RecordNr)
lastSucceedingRecordAnyThread hist =
    let myMax a b = if ts_last_record (snd a) <= ts_last_record (snd b)
                    then b
                    else a
        (tid, ts) = foldl1 myMax $ threadState hist
    in (tid, ts_last_record ts)

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
      ReplayStateOkay -> []
      ReplayStateFinished -> []
      ReplayStateFailed _ (FailureReasonControl _ threadB) ->
          let (threadA, threadALastSuccess) = lastSucceedingRecordAnyThread hist
              prefix1 = truncateHistory hist $ Finite $ threadALastSuccess
              prefix2 = truncateHistory hist $ Finite $ ts_last_but_one_record_nr $ threadState' hist threadA
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
            runMemory (truncateHistory start $ Finite $ trc_record post)
                          (trc_thread post) (trc_access post)
        (res, trc2) =
            runMemory prefix (trc_thread pre) (trc_access pre + 1)
    in dt ("flipPair " ++ (show post) ++ " " ++ (show pre)) $
       dt ("trc1 " ++ (show trc)) $
       dt ("trc2 " ++ (show trc2)) $
       res

type Goodness a = a -> Topped Integer
type Explorer a = a -> [a]

historyGoodness :: Goodness History
historyGoodness hist =
    case replayState hist of
      ReplayStateOkay -> Infinity
      ReplayStateFinished -> Infinity
      ReplayStateFailed _ (FailureReasonControl (RecordNr x) _) -> Finite x

exploreStep :: Show a => Explorer a -> Goodness a -> [(Topped Integer, a)] -> Maybe ((Topped Integer, a), [(Topped Integer, a)])
exploreStep _ _ [] = Nothing
exploreStep worker goodness ((startingGood,startingPoint):others) =
    let newHistories = worker startingPoint
        newItems = [(goodness hist, hist) | hist <- newHistories]
        newFringe = sortBy (\a b -> (fst a) `compare` (fst b)) (others ++ newItems)
    in 
       case newFringe of
         [] -> Nothing
         ((bestGoodness,_):_) ->
             {- Drop anything which is more than 1000 records behind,
                because it's not likely to be terribly useful any
                more. -}
             Just ((startingGood, startingPoint), filter (\x -> fst x > bestGoodness - 1000) newFringe)

{- Explorer from a given starting point and return the best thing we
   find -}
explore :: Show a => Explorer a -> Goodness a -> a -> a
explore worker goodness start =
    doIt (gstart, start) [(gstart, start)]
    where gstart = goodness start
          doIt (_, res) [] = dt "c4" $ res
          doIt (previousBestGoodness, previousBest) fringe =
              case exploreStep worker goodness fringe of
                Nothing -> previousBest
                Just ((Infinity, res), _) -> res
                Just ((thisGood, this), newFringe) ->
                    doIt (if thisGood > previousBestGoodness
                          then (thisGood, this)
                          else (previousBestGoodness, previousBest)) newFringe

advanceHist :: History -> History
advanceHist = explore fixControlHistoryL historyGoodness
