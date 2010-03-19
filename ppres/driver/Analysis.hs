module Analysis(
                loadOrigins, filterLoadOriginPools,
                classifierToExpression,
                exprToCriticalSections, criticalSectionToBinpatch,
                mkEnforcer, classifyFutures, autoFix) where

import Types
import History
import ReplayState()
import Timing
import Util
import Explore
import Classifier
import Reassembly

import Data.Word
import Data.List
import Numeric
import Control.Monad.Error

byteListToCString :: [Word8] -> String
byteListToCString bl = '"':(concatMap word8ToCChar bl) ++ "\""
                       where word8ToCChar x = "\\x" ++ (showHex x "")

{- All of the memory accesses made going from start to end.  The Bool
   is true for stores and false for loads. -}
memTraceTo :: History -> History -> Either String [(Bool, MemAccess)]
memTraceTo start end =
    let worker [] = return []
        worker ((TraceRecord (TraceLoad _ _ ptr _) tid acc):others) =
            do rest <- worker others
               rip <- getRipAtAccess end acc
               return $ (False, (tid, (rip, ptr))):rest
        worker ((TraceRecord (TraceStore _ _ ptr _) tid acc):others) =
            do rest <- worker others
               rip <- getRipAtAccess end acc
               return $ (True, (tid, (rip, ptr))):rest
        worker (_:others) = worker others
    in traceTo start end >>= worker

{- Run from prefix to hist, recording every load, and, for every load,
   where the data loaded came from.  This will be either Nothing if it
   was imported, or Just MemAccess if it came from a store. -}
loadOrigins :: History -> History -> Either String [(MemAccess, Maybe MemAccess)]
loadOrigins prefix hist =
    let worker [] = []
        worker ((False, acc):others) =
            let store = find (\acc' -> (snd $ snd acc) == (snd $ snd acc')) [a | (True, a) <- others]
            in (acc, store):(worker others)
        worker (_:others) = worker others
    in fmap (reverse . worker . reverse) $ memTraceTo prefix hist


{- Filter the results of loadOrigins, assuming that the first argument
   is from running loadOrigins over a bunch of runs which crashed and
   the second is from running it over a bunch of runs which didn't
   crash.  We try to remove the boring accesses, where an access is
   defined to be boring if:

   a) It has the same origin every time it appears.
 -}
filterLoadOriginPools :: [[(MemAccess, Maybe MemAccess)]] -> [[(MemAccess, Maybe MemAccess)]] -> ([[(MemAccess, Maybe MemAccess)]], [[(MemAccess, Maybe MemAccess)]])
filterLoadOriginPools poolA poolB =
    let poolA' = map sort poolA
        poolB' = map sort poolB
        pool = concat $ poolA' ++ poolB'
        accesses = fastNub $ map fst pool
        originsForAcc acc = fastNub $ map snd $ filter ((==) acc . fst) pool
        origins = [(acc, originsForAcc acc) | acc <- accesses]
        isBoring acc =
            case lookup acc origins of
              Nothing -> error "Huh? lost an access in filterLoadOriginPools"
              Just [] -> error "access with no origin"
              Just [_] -> True
              Just (_:_:_) -> False
        removeBoring :: [(MemAccess, Maybe MemAccess)] -> [(MemAccess, Maybe MemAccess)]
        removeBoring = filter (not . isBoring . fst)
    in (map removeBoring poolA', map removeBoring poolB')


{- Try to extract a critical sections list from a scheduling
   constraint expression.  The representation of critical sections
   here is as a list of pairs of RIPs.  A thread enters a critical
   section whenever it steps on the first RIP in a pair, and exits
   when it steps on the second one, and all critical sections must be
   atomic with respect to each other.  Whoever turns the CS list into
   a patch is responsible for doing enough analysis to be sure that
   all locks eventually get dropped.  If they discover that there's a
   branch out of the critical section then they should drop the lock
   at that point. -}
{- We only handle one very simple special case: X:A<Y:B & Y:C<X:D gets
   turned into two critical sections, one covering A->D and one
   covering B->C. -}
exprToCriticalSections :: BooleanExpression SchedulingConstraint -> Maybe [(Word64, Word64)]
exprToCriticalSections (BooleanAnd (BooleanLeaf (SchedulingConstraint xa yb))
                                   (BooleanLeaf (SchedulingConstraint yc xd)))
    | fst xa == fst xd && fst yb == fst yc =
        Just [(fst $ snd xa, fst $ snd xd),
              (fst $ snd yb, fst $ snd yc)]
exprToCriticalSections _ = Nothing

asmLabelToC :: AssemblyLabel -> String
asmLabelToC (AssemblyLabelOffset i) = "{bpl_offset, " ++ (show i) ++ "}"
asmLabelToC (AssemblyLabelSymbol s) = "{bpl_absolute, (unsigned long)" ++ s ++ "}" {- the compiler will do the lookup for us -}
asmLabelToC (AssemblyLabelAbsolute s) = "{bpl_absolute, 0x" ++ (showHex s "") ++ "}"

relocToC :: AssemblyReloc -> String
relocToC ar =
    "{" ++ (show $ as_offset ar) ++ ", " ++
           (show $ as_addend ar) ++ ", " ++
           (show $ as_size ar) ++ ", " ++
           (case as_relative ar of
              True -> "1"
              False -> "0") ++ ", " ++
           (asmLabelToC $ as_target ar) ++ "}"

reassemblyToC :: String -> (Word64, [Word8], [AssemblyReloc], a) -> String
reassemblyToC ident (rip, payload, relocs, _) =
    "struct binpatch_fixup " ++ ident ++ "_fixups[] = {\n        " ++
              (foldr (\a b -> a ++ ",\n        " ++ b) "" $ map relocToC relocs) ++
    "};\n" ++
    "struct binpatch " ++ ident ++ " __attribute__ ((section (\"fixup_table\"))) = {\n" ++
    "        0x" ++ (showHex rip "") ++ ",\n" ++
    "        " ++ byteListToCString payload ++ ",\n" ++
    "        " ++ (show $ length payload) ++ ",\n" ++
    "        " ++ ident ++ "_fixups,\n" ++
    "        " ++ (show $ length relocs) ++ "\n" ++
    "};\n"

criticalSectionToBinpatch' :: String -> History -> Word64 -> Word64 -> Either String String
criticalSectionToBinpatch' ident hist start end =
    do cfg <- buildCFG hist start end
       res <- reassemble hist start (map fst cfg)
       return $ reassemblyToC ident res

criticalSectionToBinpatch :: History -> Word64 -> Word64 -> Either String String
criticalSectionToBinpatch = criticalSectionToBinpatch' "myIdent"

loToBinpatch :: History -> [[(MemAccess, Maybe MemAccess)]] -> [[(MemAccess, Maybe MemAccess)]] -> Maybe String
loToBinpatch hist crash_origins nocrash_origins =
    let int = filterLoadOriginPools crash_origins nocrash_origins
        predictors = mkBinaryClassifier (fst int) (snd int)
        classifiers = map classifierToExpression predictors
        critsects = map exprToCriticalSections classifiers
        mkBinpatch :: [(Word64, Word64)] -> Either String String
        mkBinpatch ranges =
            fmap concat $ sequence [criticalSectionToBinpatch' ident hist enter exit | ((enter,exit),ident) <- zip ranges ["ident_" ++ (show x) | x <- [(0::Int)..]]]
        deMaybe :: [Maybe a] -> [a]
        deMaybe = foldr (\item acc ->
                             case item of
                               Just x -> x:acc
                               Nothing -> acc) []

        deEither :: [Either b a] -> [a]
        deEither = foldr (\item acc ->
                             case item of
                               Right x -> x:acc
                               Left _ -> acc) []

        patches = deEither $ map mkBinpatch $ deMaybe critsects
    in tlog ("predictors " ++ (show predictors)) $
       tlog ("classifiers " ++ (show classifiers)) $
       tlog ("crit sects " ++ (show critsects)) $
       case patches of
         [] -> Nothing
         x:_ -> Just x

{- Make a binpatch which will stop the bad histories from recurring
   while leaving the good histories possible. -}
mkEnforcer :: History -> [History] -> [History] -> Either String (Maybe String)
mkEnforcer hist bad_histories good_histories =
    let bad_origins = mapM (loadOrigins hist) bad_histories
        good_origins = mapM (loadOrigins hist) good_histories
    in do b <- bad_origins
          g <- good_origins
          return $ loToBinpatch hist b g

classifyFutures :: History -> ([History], [History])
classifyFutures start =
    let allFutures = enumerateHistories start
        allFutureStates = zip allFutures $ map replayState allFutures
        interestingFutureStates = filter (isInteresting . snd) allFutureStates
                                  where isInteresting (ReplayStateOkay _) = False
                                        isInteresting (ReplayStateFailed _ _ _ (FailureReasonWrongThread _)) = False
                                        isInteresting _ = True
        crashes = filter (crashed.fst) interestingFutureStates
                  where crashed hist = or $ map (ts_crashed . snd) $ threadState hist
        lastCrash = last $ sort $ map (rs_access_nr . snd) crashes
        nocrash = filter (survivesTo (lastCrash + 1) . snd) interestingFutureStates
                  where survivesTo acc s =
                            {- Strictly speaking, we should be
                               checking whether any threads have
                               crashed, but we kind of know they
                               haven't because we're past lastCrash,
                               and it's all okay. -}
                            rs_access_nr s >= acc
    in case crashes of
         [] -> ([], []) {- lastCrash, and hence nocrash, is _|_ if crashes is [] -}
         _ -> (map fst crashes, map fst nocrash)

{- Given a history which crashes, generate a binpatch which would make
   it not crash. -}
autoFix :: History -> Either String String
autoFix hist =
    let baseThreshold = rs_access_nr $ replayState hist
        tryThreshold thresh =
            tlog ("tryThreshold " ++ (show thresh)) $ 
            let t = deError $ truncateHistory hist $ Finite thresh in
            case classifyFutures t of
              ([], _) ->
                  {- hist's truncation doesn't have any crashing
                     futures -> hist didn't crash -> we can't fix
                     it. -}
                  Left "trying to fix a working history?"
              (_, []) ->
                  {- Every possible future of hist's truncation crashes ->
                     we need to backtrack further -}
                  tryThreshold (thresh - 10)
              (crashes, nocrashes) ->
                  case mkEnforcer t crashes nocrashes of
                    Left e -> Left e
                    Right Nothing -> tryThreshold (thresh - 1)
                    Right (Just m) -> Right m
    in tryThreshold baseThreshold
