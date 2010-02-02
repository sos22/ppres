module Analysis(findRacingAccesses, findControlFlowRaces, fixControlHistory,
                fixControlHistory', findCritPairs) where

import Types
import WorkerCache
import Expression()
import History
import ReplayState()

import Debug.Trace
import Data.Bits
import Data.Word
import Data.List

dt :: String -> b -> b
dt = const id


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
      ReplayStateFailed _ (FailureReasonControl nr_records dead_thread) ->
          let prefix = truncateHistory start (nr_records-1)
              criticalExpressions' = controlTrace prefix (-1)
              criticalExpressions = [(e, evalExpressionWithStore e []) | e <- criticalExpressions']
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
                  let (Just probe) = run (fst $ runMemory prefix thr (acc + 1)) (-1)
                  in (probe, dt ("Trying probe " ++ (show probe)) replayState probe)
              allProbes = map tryStore interestingStores
              probeIsGood (_, ReplayStateOkay) = True
              probeIsGood (_, ReplayStateFailed _ (FailureReasonControl progress _)) =
                  progress > nr_records
              goodProbes = filter probeIsGood allProbes
              probeIsVeryGood (_, ReplayStateOkay) = True
              probeIsVeryGood (_, ReplayStateFailed _ (FailureReasonControl progress _)) =
                  progress > nr_records + 100
              compareFailureReasons ReplayStateOkay _ = LT
              compareFailureReasons _ ReplayStateOkay = GT
              compareFailureReasons (ReplayStateFailed _ (FailureReasonControl proga _))
                                    (ReplayStateFailed _ (FailureReasonControl progb _)) =
                                        compare proga progb
              sortedProbes = sortBy ordering goodProbes
                             where ordering (_, ra) (_, rb) = compareFailureReasons ra rb
          in dt ("critical expressions " ++ (show criticalExpressions)) $
             dt ("otherStoresForThread 1 " ++ (show $ otherStoresForThread 1)) $
             dt ("otherStoresForThread 2 " ++ (show $ otherStoresForThread 2)) $
             dt ("interestingStores " ++ (show interestingStores)) $
             dt ("probes " ++ (show allProbes)) $
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

findCritPairs :: History -> [(TraceLocation, Expression)]
findCritPairs hist =
    case replayState hist of
      ReplayStateOkay -> []
      ReplayStateFailed _ (FailureReasonControl nr_records dead_thread) ->
          let prefix1 = truncateHistory hist (nr_records - 1)
              prefix2 = truncateHistory hist (nr_records - 2)
              ctrl_expressions = controlTrace prefix1 (-1)
              other_threads = filter ((/=) dead_thread) $ live_threads hist
              store_trace t = [(ptr, val, when) | (TraceRecord (TraceStore val _ ptr _) when) <- snd $ traceThread prefix2 t]
              store_changes_expr expr (ptr, val, _) =
                  evalExpressionInSnapshot expr prefix2 [] /= evalExpressionInSnapshot expr prefix2 [(ptr, val)]
              critical_pairs = [(st, expr) | expr <- ctrl_expressions, t <- other_threads, st <- store_trace t,
                                             store_changes_expr expr st]
          in [(l, e) | ((_, _, l), e) <- critical_pairs]
