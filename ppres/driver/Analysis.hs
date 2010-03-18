module Analysis(
                loadOrigins, filterLoadOriginPools,
                mkBinaryClassifier, classifierToExpression,
                exprToCriticalSections, criticalSectionToBinpatch,
                mkEnforcer, classifyFutures, autoFix) where

import Types
import WorkerCache
import History
import ReplayState()
import Timing
import Util
import Explore

import Data.Bits
import Data.Word
import Data.List
import Numeric
import Control.Monad.State
import Control.Monad.Error

import qualified Debug.Trace

dt :: String -> a -> a
dt = Debug.Trace.trace

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

stripPrefixesAssembly :: Word64 -> ErrorT String AssemblyMonad (Word64, InstructionPrefixes, [Word8])
stripPrefixesAssembly rip =
    do s <- lift get
       case stripPrefixes (as_snapshot s) rip of
         Left e -> throwError e
         Right x -> return x

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

byteListToInteger :: [Word8] -> Word64
byteListToInteger = foldr (\a b -> a + b * 256) 0 . map fromIntegral

{- Parse up a modrm sequence enough to discover its length and the extension field. -}
parseModrm :: History -> Word64 -> Word64 -> Either String (Word64, Word8)
parseModrm snapshot addr immediateBytes =
    do (len, reg) <- evalState (runErrorT (reassembleModrm addr immediateBytes)) $ AssemblyState { as_binary = [],
                                                                                                   as_relocs = [],
                                                                                                   as_ripmap = [],
                                                                                                   as_branch_targets = [],
                                                                                                   as_final_ripmap = [],
                                                                                                   as_snapshot = snapshot }
       return (addr + fromIntegral len, fromIntegral reg)

{- Parse up a modrm sequence and re-emit it.  Returns the length of
   the sequence and the register field of the modrm. -}
reassembleModrm :: Word64 -> Word64 -> ErrorT String AssemblyMonad (Int, Int)
reassembleModrm startOfModrm immediateBytes =
    do modrm <- assembleFetchByte startOfModrm
       lift $ assembleByte modrm
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
        then do sib <- assembleFetchByte $ startOfModrm + 1
                lift $ assembleByte sib
                let sibBase = bitSlice sib 0 2
                    sibDispSize = if sibBase == 5
                                  then case modfield of
                                         0 -> 4
                                         1 -> 1
                                         2 -> 4
                                         _ -> error "bitSlice not working"
                                  else 0
                if sibDispSize /= 0 && modrmDispSize /= 0 && sibDispSize /= modrmDispSize
                 then throwError $ "bad modrm decode at " ++ (showHex startOfModrm "") ++ ": modrm disp size doesn't match SIB disp size"
                 else let dispSize = if sibDispSize /= 0
                                     then sibDispSize
                                     else modrmDispSize
                          addend = immediateBytes + dispSize
                      in do dispBytes <- assembleFetchBytes (startOfModrm + 2) dispSize
                            lift $ if ripRelative
                             then do emitRelocR 0 (fromIntegral dispSize) addend $ AssemblyLabelAbsolute (startOfModrm + 2 + addend + byteListToInteger dispBytes)
                                     assembleBytes (take (fromIntegral dispSize) $ repeat 0)
                             else assembleBytes dispBytes
                            return (fromIntegral $ dispSize + 2, fromIntegral $ regfield)
        else let dispSize = modrmDispSize in
             do dispBytes <- assembleFetchBytes (startOfModrm + 1) modrmDispSize
                lift $ if ripRelative
                 then do emitRelocR 0 (fromIntegral dispSize) (immediateBytes + dispSize) $ AssemblyLabelAbsolute (startOfModrm + 1 + immediateBytes + dispSize + byteListToInteger dispBytes)
                         assembleBytes (take (fromIntegral dispSize) $ repeat 0)
                 else assembleBytes dispBytes
                return (fromIntegral $ dispSize + 1, fromIntegral $ regfield)

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


{- Like nub, but O(nlogn) rather than O(n^2), and only works on
   totally ordered values. -}
fastNub :: Ord a => [a] -> [a]
fastNub = map head . group . sort

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


{- Build every possible classifier which is consistent with the list
   of samples and which doesn't just invent stuff out of thin air.
   The samples must be consistent, but they do not have to be
   complete.  If they are not complete, we'll take the nearest
   available result, for some vaguely sensible definition of
   nearest. -}
mkClassifier :: (Ord result, Ord key, Ord value) => [([(key,value)],result)] -> [(Classifier key value result)]
mkClassifier samples =
    let availresults = fastNub $ map snd samples
        allkeys = fastNub $ map fst $ concatMap fst samples
        valuesForKey k = fmap fastNub $ sequence $ map (lookup k . fst) samples
        availkeys = 
            {- A key must be present in every sample in order to be
               used as a discriminant, and must have multiple
               potential values. -}
            filter keyIsUsable allkeys
            where
              keyIsUsable k = case valuesForKey k of
                                Nothing -> False
                                Just [] -> error "Huh?"
                                Just [_] -> False
                                _ -> True
    in case availresults of
         [] -> []
         [x] -> return $ ClassifierLeaf x
         _ -> {- Multiple possible results, do it properly -}
              do discriminant <- availkeys
                 let fmaybe = maybe undefined id
                     flookup k kvs = fmaybe $ lookup k kvs
                     childForValue v =
                         mkClassifier [ ([kvs | kvs <- fst s, fst kvs /= discriminant], snd s)
                                        | s <- samples, flookup discriminant (fst s) == v]
                     clistEntryForValue v =
                         do c <- childForValue v
                            return (v, c)
                     children = sequence $ map clistEntryForValue $ fmaybe $ valuesForKey discriminant
                 c <- children
                 return $ ClassifierChoice discriminant c

mkBinaryClassifier :: (Ord key, Ord value) => [[(key,value)]] -> [[(key, value)]] -> [(Classifier key value Bool)]
mkBinaryClassifier true false =
    mkClassifier $ (zip true $ repeat True) ++ (zip false $ repeat False)


boolNot :: BooleanExpression t -> BooleanExpression t
boolNot (BooleanConst False) = BooleanConst True
boolNot (BooleanConst True) = BooleanConst False
boolNot x = BooleanNot x

boolAnd :: BooleanExpression t -> BooleanExpression t -> BooleanExpression t
boolAnd (BooleanConst False) _ = BooleanConst False
boolAnd (BooleanConst True) x = x
boolAnd _ (BooleanConst False) = BooleanConst False
boolAnd x (BooleanConst True) = x
boolAnd x y = BooleanAnd x y

boolOr :: BooleanExpression t -> BooleanExpression t -> BooleanExpression t
boolOr (BooleanConst False) x = x
boolOr (BooleanConst True) _ = BooleanConst True
boolOr x (BooleanConst False) = x
boolOr _ (BooleanConst True) = BooleanConst True
boolOr x y = BooleanOr x y

liftB :: t -> BooleanExpression t
liftB = BooleanLeaf

constB :: Bool -> BooleanExpression t
constB = BooleanConst

foldBooleanExpression :: BooleanExpressionFolder s t -> BooleanExpression s -> t
foldBooleanExpression f (BooleanLeaf s) = bef_leaf f s
foldBooleanExpression f (BooleanConst b) = bef_const f b
foldBooleanExpression f (BooleanOr l r) =
    bef_or f (foldBooleanExpression f l) (foldBooleanExpression f r)
foldBooleanExpression f (BooleanAnd l r) =
    bef_and f (foldBooleanExpression f l) (foldBooleanExpression f r)
foldBooleanExpression f (BooleanNot l) =
    bef_not f (foldBooleanExpression f l)

nopBefFolder :: BooleanExpressionFolder t (BooleanExpression t)
nopBefFolder = BooleanExpressionFolder { bef_leaf = liftB,
                                         bef_const = constB,
                                         bef_or = boolOr,
                                         bef_and = boolAnd,
                                         bef_not = boolNot }

classifierToExpression :: Classifier MemAccess (Maybe MemAccess) Bool -> BooleanExpression SchedulingConstraint
classifierToExpression (ClassifierLeaf r) = constB r
classifierToExpression (ClassifierChoice discriminant options) =
    let values = map fst options
        nullaryValue = boolNot $ foldr1 boolAnd [liftB $ SchedulingConstraint v discriminant | Just v <- values]
        exprForValue (v,c) =
            (case v of
               Nothing -> nullaryValue
               Just v' -> liftB $ SchedulingConstraint v' discriminant) `boolAnd`
            (classifierToExpression c)
        simplify = foldBooleanExpression $ nopBefFolder { bef_not = simplify_not }
                   where simplify_not (BooleanLeaf (SchedulingConstraint a b)) = BooleanLeaf $ SchedulingConstraint b a
                         simplify_not x = boolNot x
    in simplify $ foldr1 boolOr $ map exprForValue options


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

data InstructionTemplate =
    InstructionTemplate {

      {- Get the following instructions for this instruction. -}
      it_next_instr :: History -> Word64 -> InstructionPrefixes -> Either String [Word64],

      it_reassemble :: Word64 -> InstructionPrefixes -> ErrorT String AssemblyMonad (Maybe Word64)
    }

instruction_templates :: [(Word8, InstructionTemplate)]
instruction_templates =
    let next_instr_just_modrm opcodeLen snapshot rip _ =
            do (nrip, _) <- parseModrm snapshot (rip + opcodeLen) 0
               return [nrip]
        next_instr_modrm_imm imm opcodeLen snapshot rip prefixes =
            do r <- next_instr_just_modrm opcodeLen snapshot rip prefixes
               return $ map (+ imm) r
        next_instr_jcc snapshot rip _ =
            do b <- byte snapshot $ rip + 1
               let b' = if b < 0x80 then toInteger b
                        else (toInteger b) - 0x100
                   fall_through = rip + 2
               return [fall_through, fall_through + (fromInteger b')]

        next_instr_group5 snapshot rip _ =
            do (nrip, extension) <- parseModrm snapshot (rip + 1) 0
               case extension of
                 2 -> {- Call indirect.  We cheat a bit and just return the next instruction. -}
                      return [nrip]
                 _ -> Left $ "unknown group 5 instruction " ++ (show extension)
        
        next_instr_group11 snapshot rip prefixes =
            let immsize = if ip_opsize prefixes
                          then 2
                          else 4
            in do (nrip, _) <- parseModrm snapshot (rip + 1) immsize
                  return [nrip + immsize]
        
        next_instr_fixed_length l _ rip _ =
            return [rip + l]

        next_instr_ret _ _ _ = return []

        reassemble_jcc :: Word64 -> InstructionPrefixes -> ErrorT String AssemblyMonad (Maybe Word64)
        reassemble_jcc rip _ =
            do hbyte <- assembleFetchByte rip
               offset8 <- assembleFetchByte $ rip + 1
               let offset8' = if offset8 > 0x80
                              then toInteger offset8 - 0x100
                              else toInteger offset8
                   targ = fromInteger $ (toInteger rip) + offset8' + 2
               {- We turn all 8 bit jcc instructions into 32 bit ones,
                  for sanity. -}
               lift $ do assembleByte 0x0f
                         assembleByte $ case hbyte of
                                          0x75 -> 0x85 {- jne -}
                                          _ -> error $ "bad 8 bit jcc " ++ (showHex hbyte "")
                         assembleRelRip32 targ 0
               return $ Just $ rip + 2

        reassemble_modrm_imm immSz opcodeLen rip _ =
            do hbyte <- assembleFetchByte rip
               lift $ assembleByte hbyte
               (modrmsize, _) <- reassembleModrm (rip + opcodeLen) immSz
               imm <- assembleFetchBytes (rip + (fromIntegral modrmsize) + opcodeLen) immSz
               lift $ assembleBytes imm
               return $ Just $ rip + (fromIntegral modrmsize) + opcodeLen + immSz

        reassemble_group11 = reassemble_modrm_imm 4 1
        reassemble_just_modrm = reassemble_modrm_imm 0
        reassemble_ret rip _ =
            do hbyte <- assembleFetchByte rip
               lift $ assembleByte hbyte
               return Nothing
        reassemble_fixed_length len rip _ =
            do hbyte <- assembleFetchBytes rip len
               lift $ assembleBytes hbyte
               return $ Just $ rip + len
        reassemble_group5 rip _ =
            do hbyte <- assembleFetchByte rip
               lift $ assembleByte hbyte
               (modrmsize, extension) <- reassembleModrm (rip + 1) 0
               case extension of
                 2 -> {- Call indirect.  As in next_instr_group5, we ignore the control flow
                         transfer and just assume the callee's going to immediately return. -}
                      return $ Just $ rip + fromIntegral modrmsize + 1
                 _ -> throwError $ "unknown group 5 instruction " ++ (show extension)
        
    in
    [(0x75, InstructionTemplate { it_next_instr = next_instr_jcc,
                                  it_reassemble = reassemble_jcc }),
     (0x83, InstructionTemplate { it_next_instr = next_instr_modrm_imm 1 1,
                                  it_reassemble = reassemble_modrm_imm 1 1}),
     (0x89, InstructionTemplate { it_next_instr = next_instr_just_modrm 1,
                                  it_reassemble = reassemble_just_modrm 1}),
     (0x8b, InstructionTemplate { it_next_instr = next_instr_just_modrm 1 ,
                                  it_reassemble = reassemble_just_modrm 1} ),
     (0xc3, InstructionTemplate { it_next_instr = next_instr_ret,
                                  it_reassemble = reassemble_ret }),
     (0xc7, InstructionTemplate { it_next_instr = next_instr_group11,
                                  it_reassemble = reassemble_group11 }),
     (0xc9, InstructionTemplate { it_next_instr = next_instr_fixed_length 1,
                                  it_reassemble = reassemble_fixed_length 1}),
     (0xff, InstructionTemplate { it_next_instr = next_instr_group5,
                                  it_reassemble = reassemble_group5 }) ]

{- Start at start and explore until we get to end, or something bad
   happens and we can't explore any more. -}
{- Ultimate aim is to build a CFG rooted at start which shows as many
   of the ``short'' paths to end as possible, for some suitable
   definition of short. -}

{- For the purposes of the CFG, an instruction can be represented by a
   list of all of its outgoing edges.  We also include a list of all
   the incoming edges, because that makes everything easier. -}
data Instruction = Ins [Word64] [Word64] deriving Show

buildCFG :: History -> Word64 -> Word64 -> Either String [(Word64, Instruction)]
buildCFG snapshot start end =
    let 
        exitsOfInstruction rip =
            do (after_prefix_rip, prefixes, _) <- stripPrefixes snapshot rip
               hbyte <- byte snapshot after_prefix_rip
               case lookup hbyte instruction_templates of
                 Nothing -> Left $ "don't know what to do with hbyte 0x" ++ (showHex hbyte "") ++ " at 0x" ++ (showHex rip "")
                 Just t -> it_next_instr t snapshot after_prefix_rip prefixes

        mkCFG whiteInstructions [] = return whiteInstructions
        mkCFG whiteInstructions (rip:greyInstructions) = 
            do exits <- exitsOfInstruction rip
               let newWhite = (rip, Ins exits undefined):whiteInstructions
                   newGrey = foldr discover greyInstructions exits
                             where discover newRip currentGrey =
                                       if newRip `elem` currentGrey
                                       then currentGrey
                                       else case lookup newRip whiteInstructions of
                                              Nothing -> newRip:currentGrey
                                              _ -> currentGrey
               mkCFG newWhite newGrey
        
        addIncomingEdges :: [(Word64, Instruction)] -> [(Word64, Instruction)]
        addIncomingEdges ins =
            let getIncomingEdges addr =
                    [a | (a, Ins o _) <- ins, addr `elem` o]
            in [(addr, Ins outgoing $ getIncomingEdges addr) |
                (addr, Ins outgoing _) <- ins]

        {- Trim the CFG so that it only includes instructions which
           can reach the target. -}
        trimCFG :: [(Word64, Instruction)] -> [(Word64, Instruction)]
        trimCFG cfg =
            let findRelevantRips white [] = white
                findRelevantRips white (rip:gray) =
                    let newWhite = rip:white
                    in case lookup rip cfg of
                         Nothing -> error "lost a RIP"
                         Just (Ins _ incoming) ->
                             let newGray = foldr discover gray incoming
                                 discover newGry oldGray =
                                     if newGry `elem` newWhite || newGry `elem` oldGray
                                     then oldGray
                                     else newGry:oldGray
                             in findRelevantRips newWhite newGray
                relevantRips = findRelevantRips [] [end]
            in filter (flip elem relevantRips . fst) cfg

    in fmap (trimCFG . addIncomingEdges) $ mkCFG [(end, Ins [] undefined)] [start]

{- Either an offset in the assembly, or an actual RIP, or a symbol. -}
data AssemblyLabel = AssemblyLabelOffset Int
                   | AssemblyLabelSymbol String
                   | AssemblyLabelAbsolute Word64
                     deriving Show

data AssemblyReloc = AssemblyReloc { as_offset :: Int,
                                     as_target :: AssemblyLabel,
                                     as_addend :: Word64,
                                     as_size :: Int,
                                     as_relative :: Bool } deriving Show

data AssemblyState = AssemblyState {
      as_binary :: [Word8],
      as_relocs :: [AssemblyReloc],
      as_ripmap :: [(Word64, Int)],
      as_branch_targets :: [Word64],
      as_final_ripmap :: [(Word64, Int)],
      as_snapshot :: History
    }

type AssemblyMonad = State AssemblyState

assembleFetchByte :: Word64 -> ErrorT String AssemblyMonad Word8
assembleFetchByte addr =
    do s <- lift get
       let snapshot = as_snapshot s
       case byte snapshot addr of
         Left e -> throwError e
         Right x -> return x

assembleFetchBytes :: Word64 -> Word64 -> ErrorT String AssemblyMonad [Word8]
assembleFetchBytes addr size =
    do s <- lift get
       let snapshot = as_snapshot s
       case bytes snapshot addr size of
         Left e -> throwError e
         Right x -> return x

assembleByte :: Word8 -> AssemblyMonad ()
assembleByte b =
    modify $ \s -> s { as_binary = as_binary s ++ [b] }

assembleBytes :: [Word8] -> AssemblyMonad ()
assembleBytes = mapM_ assembleByte

getLabelForRip :: Word64 -> AssemblyMonad AssemblyLabel
getLabelForRip rip =
    do s <- get
       if not $ rip `elem` (as_branch_targets s)
          then put $ s { as_branch_targets = rip:(as_branch_targets s) }
          else return ()
       return $ case lookup rip $ as_final_ripmap s of
                  Nothing -> error "lost a RIP"
                  Just t -> AssemblyLabelOffset t

assembleRelRip32 :: Word64 -> Word64 -> AssemblyMonad ()
assembleRelRip32 targ addend =
    do l <- getLabelForRip targ
       emitRelocR 0 4 (addend + 4) l
       assembleBytes [0,0,0,0]

assembleOffset :: AssemblyMonad Int
assembleOffset = liftM (length . as_binary) get 

{- Say that the thing offset bytes ahead of the current point, of size
   size, should be relocated to point at the given label. -}
emitReloc :: Int -> Int -> AssemblyLabel -> AssemblyMonad ()
emitReloc offset size target =
    do rip <- assembleOffset
       let ar = AssemblyReloc { as_offset = offset + rip,
                                as_target = target,
                                as_addend = 0,
                                as_size = size,
                                as_relative = False }
       modify $ \s -> s { as_relocs = ar:(as_relocs s) }

{- Similar, but relative with an addend. -}
emitRelocR :: Int -> Int -> Word64 -> AssemblyLabel -> AssemblyMonad ()
emitRelocR offset size addend target =
    do rip <- assembleOffset
       let ar = AssemblyReloc { as_offset = offset + rip,
                                as_target = target,
                                as_addend = addend,
                                as_size = size,
                                as_relative = True }
       modify $ \s -> s { as_relocs = ar:(as_relocs s) }

{- Take an assembly monad and tweak it so that we put an instruction
   boundary right at the start. -}
instruction :: Word64 -> ErrorT String AssemblyMonad a -> ErrorT String AssemblyMonad a
instruction rip content =
    do ofs <- lift assembleOffset
       lift $ modify $ \s -> s { as_ripmap = (rip,ofs):(as_ripmap s) }
       content

reassembleInstruction :: Word64 -> ErrorT String AssemblyMonad (Maybe Word64)
reassembleInstruction rip =
    do (after_prefix_rip, prefixes, prefixBytes) <- stripPrefixesAssembly rip
       lift $ assembleBytes prefixBytes
       hbyte <- assembleFetchByte after_prefix_rip
       case lookup hbyte instruction_templates of
         Nothing -> throwError $ "don't know what to do with hbyte 0x" ++ (showHex hbyte "") ++ " at 0x" ++ (showHex rip "") ++ " while reassembling"
         Just t ->
             dt ("reassembling around " ++ (showHex rip "")) $
             it_reassemble t after_prefix_rip prefixes

{- Do reassembly starting from rip until the doInstr worker tells us
   there are no more fall-throughs.  Out of line branchs are
   accumulated in the AssemblyMonad. -}
reassembleStraightLine :: Word64 -> (Word64 -> ErrorT String AssemblyMonad (Maybe Word64)) -> ErrorT String AssemblyMonad ()
reassembleStraightLine rip doInstr =
    do fallThrough <- doInstr rip
       case fallThrough of
         Just rip' -> reassembleStraightLine rip' doInstr
         Nothing -> return ()

{- While we have unhandled out-of-line chunks, pick one and run worker
   on it. -}
handleOutOfLines :: (Word64 -> ErrorT String AssemblyMonad ()) -> ErrorT String AssemblyMonad ()
handleOutOfLines worker =
    do s <- lift get
       let done_rips = map fst $ as_ripmap s
           undone_rips = as_branch_targets s \\ done_rips
       case undone_rips of
         [] -> return ()
         (rip:_) -> do worker rip
                       handleOutOfLines worker

assembleJmp :: Word64 -> AssemblyMonad ()
assembleJmp targ =
    do assembleBytes [0xe9, 0, 0, 0, 0]
       emitRelocR (-4) 4 4 (AssemblyLabelAbsolute targ)

assembleEpilogue :: Word64 -> AssemblyMonad ()
assembleEpilogue targ =
    do assembleCallSequence "critical_section_epilogue"
       assembleJmp targ

assembleCallSequence :: String -> AssemblyMonad ()
assembleCallSequence symbol =
    do assembleBytes [0x48, 0x8d, 0x64, 0x24, 0x80] {- lea -128(%rsp), %rsp -> get out of the red zone -}
       assembleBytes [0x50] {- pushq %rax -}
       assembleBytes [0x48, 0xb8, 0, 0, 0, 0, 0, 0, 0, 0] {- movq $imm64, %rax -}
       emitReloc (-8) 8 (AssemblyLabelSymbol symbol)
       assembleBytes [0xff, 0xd0] {- call *%rax -}
       assembleBytes [0x58] {- pop %rax -}
       assembleBytes [0x48, 0x8d, 0xa4, 0x24, 0x80, 0, 0, 0] {- lea 128(%rsp), %rsp -}

assemblePrologue :: AssemblyMonad ()
assemblePrologue = assembleCallSequence "critical_section_prologue"

reassemble :: History -> Word64 -> [Word64] -> Either String (Word64, [Word8], [AssemblyReloc], [(Word64, Int)])
reassemble snapshot start allowed_rips =
    let doOneInstruction rip =
            instruction rip $
            if rip `elem` allowed_rips
            then (if rip == start
                  then lift assemblePrologue
                  else return ()) >> reassembleInstruction rip
            else lift (assembleEpilogue rip) >> return Nothing
        straightLine rip = reassembleStraightLine rip doOneInstruction
        initState = AssemblyState { as_binary = [],
                                    as_relocs = [],
                                    as_ripmap = [],
                                    as_branch_targets = [start],
                                    as_final_ripmap = as_ripmap finalState,
                                    as_snapshot = snapshot }
        (finalVal, finalState) = runState (runErrorT (handleOutOfLines straightLine)) initState
    in case finalVal of
         Left e -> Left e
         Right _ -> Right (start, as_binary finalState, as_relocs finalState, as_ripmap finalState)

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

rs_access_nr :: ReplayState -> AccessNr
rs_access_nr (ReplayStateOkay x) = x
rs_access_nr (ReplayStateFinished x) = x
rs_access_nr (ReplayStateFailed _ _ x _) = x

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
