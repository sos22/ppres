module Reassembly(AssemblyLabel(..), AssemblyReloc(..), buildCFG, reassemble) where

import History

import Data.Bits
import Data.Word
import Data.List
import Numeric
import Control.Monad.State
import Control.Monad.Error

import qualified Debug.Trace

dt :: String -> a -> a
dt = Debug.Trace.trace

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

{- The core of the reassembler.  The tricky part is the mapping from
   RIPs to offsets in the binary, known as the ripmap.  There are three
   interesting bits of state:

   as_ripmap -- mapping from RIPs to offsets for instructions which
                we've reassembled already.
   as_branch_targets -- list of all the RIPs for which we will
                        eventually need a mapping.
   as_final_ripmap -- a complete mapping from RIPs to offsets.

   We run the top-level assembly monad action in a loop in order to
   build the ripmap.  Initially, as_ripmap and as_branch_targets are
   empty, and after every iteration we check whether as_branch_targets
   is a subset of as_ripmap.  If it is, that as_ripmap becomes
   as_final_ripmap via the power of laziness.  This is pretty
   convenient, but means that you have to be a little bit careful about
   forcing the final ripmap's contents. -}
data AssemblyState = AssemblyState {
      as_binary :: [Word8],
      as_relocs :: [AssemblyReloc],
      as_ripmap :: [(Word64, Int)],
      as_branch_targets :: [Word64],
      as_final_ripmap :: [(Word64, Int)],
      as_snapshot :: History
    }

type AssemblyMonad = State AssemblyState

{- For the purposes of the CFG, an instruction can be represented by a
   list of all of its outgoing edges.  We also include a list of all
   the incoming edges, because that makes everything easier. -}
data Instruction = Ins [Word64] [Word64] deriving Show

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
    InstructionPrefixes False False False False False False
                        False False False False False False
                        False False False


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

byteListToInteger :: [Word8] -> Word64
byteListToInteger = foldr (\a b -> a + b * 256) 0 . map fromIntegral

bitSlice :: Bits a => a -> Int -> Int -> a
bitSlice val start end = (val `shiftR` start) .&. ((1 `shiftL` (end - start + 1)) - 1)


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


data InstructionTemplate =
    InstructionTemplate {

      {- Get the following instructions for this instruction. -}
      it_next_instr :: History -> Word64 -> InstructionPrefixes -> Either String [Word64],

      {- Reassemble an instruction.  Parse it up, and the re-emit it
         along with a bunch of relocations so that it can be safely
         moved around. -}
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

