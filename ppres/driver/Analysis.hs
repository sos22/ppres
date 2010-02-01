module Analysis(findRacingAccesses, findControlFlowRaces, fixControlHistory) where

import Types
import WorkerCache
import Expression()
import History

import Debug.Trace
import Data.Bits
import Data.Word

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
          expressionMentionsLoad (TraceRecord (TraceLoad _ _ _ _) (TraceLocation rec acc _))
                                     (ExpressionMem _ (ExpressionCoord rec' acc') _ _) =
                                         rec == rec' && acc == acc'
          expressionMentionsLoad _ _ = error "confused"


wordSigned :: Word64 -> Integer
wordSigned w =
    if w `testBit` 63
    then (fromIntegral w) - 0x10000000000000000
    else (fromIntegral w)

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
       return $ case op of
                  BinopSub -> l - r
                  BinopAdd -> l + r
                  BinopMull -> l * r
                  BinopMullHi -> fromInteger $ (toInteger l * toInteger r) `shiftR` 64
                  BinopMullS -> error "write me"
                  BinopShrl -> fromInteger $ ((toInteger l) `shiftR` (fromIntegral r))
                  BinopShl -> l `shiftL` (fromIntegral r)
                  BinopShra -> l `shiftR` (fromIntegral r)
                  BinopAnd -> l .&. r
                  BinopOr -> l .|. r
                  BinopXor -> l `xor` r
                  BinopLe -> if wordSigned l <= wordSigned r then 1 else 0
                  BinopBe -> if l <= r then 1 else 0
                  BinopEq -> if l == r then 1 else 0
                  BinopB -> if l < r then 1 else 0
                  BinopCombine -> error "Can't happen"

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
              criticalExpressions = controlTrace prefix (-1)
              otherThreads = [x | x <- [1,2], x /= dead_thread]
              otherStoresForThread t =
                  [(ptr, val, when) | (TraceRecord (TraceStore val _ ptr _ ) when) <- snd $ traceThread start t]
              storeSatisfiesExpression (ptr,val,_) expr =
                  case fmap (1 .&.) $ evalExpressionWithStore expr [(ptr,val)] of
                    Nothing -> False
                    Just 0 -> False
                    Just 1 -> True
                    _ -> error "Huh?"
              satisfiedExpressions st =
                  [ind | (ind, expr) <- zip [0..] criticalExpressions, storeSatisfiesExpression st expr]
              interestingStores =
                  concat [[(st, ind) | st <- otherStoresForThread t, ind <- satisfiedExpressions st]
                          | t <- otherThreads]
          in
             case interestingStores of
               [] -> Nothing
               (((_, _, (TraceLocation _ acc thr)),_):_) ->
                   {- Pick the first one pretty much arbitrarily -}
                   let (Just probe) = run (fst $ runMemory prefix thr (acc+1)) (-1)
                   in case replayState probe of
                        ReplayStateOkay -> Just probe
                        (ReplayStateFailed _ (FailureReasonControl prog _)) ->
                            if prog > nr_records then Just probe
                            else Debug.Trace.trace "no progress" $ Nothing

fixControlHistory :: History -> History
fixControlHistory start =
    case fixControlHistory' start of
      Nothing -> start
      Just x -> fixControlHistory x
