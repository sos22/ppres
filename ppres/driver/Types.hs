{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Types where

import Data.Word
import Network.Socket
import Numeric
import Data.IORef

import Util

newtype ThreadId = ThreadId Integer deriving (Read, Show, Eq, Ord)
type VariableName = String

newtype RecordNr = RecordNr Integer deriving (Eq, Show, Enum, Ord, Read)
newtype AccessNr = AccessNr Integer deriving (Eq, Show, Enum, Ord, Real, Num, Read, Integral)

data Worker = Worker { worker_fd :: Socket,
                       worker_alive :: IORef Bool,
                       worker_frozen :: IORef Bool }

instance Show Worker where
    show w = "worker fd " ++ (show $ worker_fd w)

data CriticalSection = CriticalSection ThreadId [AccessNr]

data TraceEntry = TraceFootstep { trc_foot_rip :: Word64,
                                  trc_foot_rdx :: Word64,
                                  trc_foot_rcx :: Word64,
                                  trc_foot_rax :: Word64 }
                | TraceSyscall { trc_sys_nr :: Int }
                | TraceRdtsc
                | TraceLoad { trc_load_val :: Word64,
                              trc_load_size :: Int,
                              trc_load_ptr :: Word64,
                              trc_load_in_monitor :: Bool,
                              trc_rip :: Word64 }
                | TraceStore { trc_store_val :: Word64,
                               trc_store_size :: Int,
                               trc_store_ptr :: Word64,
                               trc_store_in_monitor :: Bool,
                               trc_rip :: Word64 }
                | TraceCalling { trc_calling :: String }
                | TraceCalled { trc_called :: String }
                | TraceEnterMonitor
                | TraceExitMonitor
                | TraceSignal { trc_rip :: Word64,
                                trc_signr :: Int,
                                trc_err :: Word64,
                                trc_va :: Word64 }
                  deriving (Eq)

instance Show TraceEntry where
    show (TraceFootstep rip _ _ _ ) = "footstep " ++ (showHex rip "")
    show (TraceSyscall nr) = "syscall " ++ (show nr)
    show (TraceRdtsc) = "rdtsc"
    show (TraceLoad val _ ptr mon _) =
        "load " ++ (showHex ptr $ " -> " ++ (showHex val (if mon then " monitor"
                                                          else "")))
    show (TraceStore val _ ptr mon _) =
        "store " ++ (showHex ptr $ " -> " ++ (showHex val (if mon then " monitor"
                                                           else "")))
    show (TraceCalling c) = "calling " ++ c
    show (TraceCalled c) = "called " ++ c
    show TraceEnterMonitor = "enter_monitor"
    show TraceExitMonitor = "exit_monitor"
    show (TraceSignal rip sig _ va) = "signal " ++ (show sig) ++ "@" ++ (showHex va "") ++ ", rip = " ++ (showHex rip "")

instance Read TraceEntry where
    readsPrec _ x =
        do (keyword, trail1) <- lex x
           case keyword of
             "footstep" -> do (rip, trail2) <- reads trail1
                              return (TraceFootstep rip 0 0 0, trail2)
             "syscall" -> do (nr, trail2) <- reads trail1
                             return (TraceSyscall nr, trail2)
             "rdtsc" -> return (TraceRdtsc, trail1)
             "enter_monitor" -> return (TraceEnterMonitor, trail1)
             "exit_monitor" -> return (TraceExitMonitor, trail1)
             "calling" -> do (targ, trail2) <- lex trail1
                             return (TraceCalling targ, trail2)
             "called" -> do (targ, trail2) <- lex trail1
                            return (TraceCalled targ, trail2)
             y | y == "load" || y == "store"->
                   let c = if y == "load" then TraceLoad
                           else TraceStore
                   in
                   do (ptr, trail2) <- reads trail1
                      (arrow, trail3) <- lex trail2
                      if arrow /= "->"
                        then []
                        else do (val, trail4) <- reads trail3
                                (m, trail5) <- lex trail4
                                if m == "monitor"
                                 then return (c val 0 ptr True 0, trail5)
                                 else return (c val 0 ptr False 0, trail4)
             _ -> []

data TraceRecord = TraceRecord { trc_trc :: TraceEntry,
                                 trc_tid :: ThreadId,
                                 trc_loc :: AccessNr } deriving (Show, Read, Eq)

data RegisterName = REG_RAX
                  | REG_RDX
                  | REG_RCX
                  | REG_RBX
                  | REG_RSP
                  | REG_RBP
                  | REG_RSI
                  | REG_RDI
                  | REG_R8
                  | REG_R9
                  | REG_R10
                  | REG_R11
                  | REG_R12
                  | REG_R13
                  | REG_R14
                  | REG_R15
                  | REG_CC_OP
                  | REG_CC_DEP1
                  | REG_CC_DEP2
                  | REG_CC_NDEP
                  | REG_DFLAG
                  | REG_RIP
                  | REG_IDFLAG
                  | REG_FS_ZERO
                  | REG_SSE_ROUND
                    deriving (Show, Read, Eq)

instance Forcable RegisterName where
    force = seq

newtype RegisterFile = RegisterFile [(RegisterName, Word64)] deriving Show

getRegister :: RegisterFile -> RegisterName -> Either String Word64
getRegister (RegisterFile rf) rn = case lookup rn rf of
                                     Nothing -> Left $ "huh? register file didn't have " ++ (show rn)
                                     Just x -> Right x

getRegister' :: RegisterFile -> RegisterName -> Word64
getRegister' rf rn = deError $ getRegister rf rn

data Binop = BinopCombine
           | BinopSub
           | BinopAdd
           | BinopMull
           | BinopMullHi
           | BinopMullS
           | BinopShrl
           | BinopShl
           | BinopShra
           | BinopAnd
           | BinopOr
           | BinopXor
           | BinopLe
           | BinopBe
           | BinopEq
           | BinopB deriving (Read, Show)

data Expression = ExpressionRegister RegisterName Word64
                | ExpressionConst Word64
                | ExpressionLoad ThreadId Int AccessNr Expression Expression
                | ExpressionStore ThreadId AccessNr Expression
                | ExpressionImported Word64
                | ExpressionBinop Binop Expression Expression
                | ExpressionNot Expression deriving (Read)

data ExpressionFolder a = ExpressionFolder { ef_reg :: RegisterName -> Word64 -> a,
                                             ef_const :: Word64 -> a,
                                             ef_load :: ThreadId -> Int -> AccessNr -> a -> a -> a,
                                             ef_store :: ThreadId -> AccessNr -> a -> a,
                                             ef_imported :: Word64 -> a,
                                             ef_binop :: Binop -> a -> a -> a,
                                             ef_not :: a -> a }

foldrExpression :: ExpressionFolder a -> Expression -> a
foldrExpression folder expr =
    case expr of
      ExpressionRegister n v -> ef_reg folder n v
      ExpressionConst v -> ef_const folder v
      ExpressionLoad tid sz when addr val ->
          ef_load folder tid sz when (foldrExpression folder addr) (foldrExpression folder val)
      ExpressionStore tid when val ->
          ef_store folder tid when $ foldrExpression folder val
      ExpressionImported v -> ef_imported folder v
      ExpressionBinop op l r ->
          ef_binop folder op (foldrExpression folder l) (foldrExpression folder r)
      ExpressionNot e -> ef_not folder $ foldrExpression folder e

showW64 :: Word64 -> String
showW64 w = if w > 100
            then "0x" ++ (showHex w "")
            else show w

instance Show Expression where
    show (ExpressionRegister rname val) = shows rname $ ':' : (showW64 val)
    show (ExpressionConst val) = showW64 val
    show (ExpressionLoad tid sz when addr val) = "load" ++ (show sz) ++ "@(" ++ (show tid) ++ ":" ++ (show when) ++ ")[" ++ (show addr) ++ "]:(" ++ (show val) ++ ")"
    show (ExpressionStore tid when val) = "store@(" ++ (show tid) ++ ":" ++ (show when) ++ "):(" ++ (show val) ++ ")"
    show (ExpressionImported val) = "IMPORT:" ++ (showW64 val)
    show (ExpressionBinop op l r) = (show op) ++ " (" ++ (show l) ++ ") (" ++ (show r) ++ ")"
    show (ExpressionNot e) = "~(" ++ (show e) ++ ")"

data ReplayFailureReason = FailureReasonControl 
                         | FailureReasonWrongThread ThreadId {- The thread we wanted; the one we got is in ReplayStateFailed -}
                         | FailureReasonData Expression Expression deriving (Show, Read)

data ReplayState = ReplayStateOkay AccessNr
                 | ReplayStateFinished AccessNr
                 | ReplayStateFailed String ThreadId AccessNr ReplayFailureReason deriving (Show, Read)

rs_access_nr :: ReplayState -> AccessNr
rs_access_nr (ReplayStateOkay x) = x
rs_access_nr (ReplayStateFinished x) = x
rs_access_nr (ReplayStateFailed _ _ x _) = x

data ThreadState = ThreadState { ts_dead :: Bool, {- exitted normally -}
                                 ts_crashed :: Bool, {- died with a segv etc. -}
                                 ts_last_run :: AccessNr,
                                 ts_last_rip :: Word64 } deriving (Show, Eq)

data Topped x = Infinity
              | Finite !x deriving Eq

instance Functor Topped where
    fmap _ Infinity = Infinity
    fmap f (Finite x) = Finite $ f x

instance Show x => Show (Topped x) where
    show Infinity = "inf"
    show (Finite x) = show x

instance Read x => Read (Topped x) where
    readsPrec _ x =
        do (keyword, trail) <- lex x
           if keyword == "inf"
              then return (Infinity, trail)
              else map (first Finite) $ reads x

instance Num x => Num (Topped x) where
    Infinity + _ = Infinity
    _ + Infinity = Infinity
    (Finite x) + (Finite y) = Finite $ x + y

    Infinity - Infinity = error "difference of two infinities"
    Infinity - (Finite _) = Infinity
    (Finite _) - Infinity = error "negative infinity"
    (Finite x) - (Finite y) = Finite $ x - y

    Infinity * (Finite 0) = error "multiply infinity by zero"
    (Finite 0) * Infinity = error "multiply infinity by zero"
    Infinity * _ = Infinity
    _ * Infinity = Infinity
    (Finite x) * (Finite y) = Finite $ x * y

    abs Infinity = Infinity
    abs (Finite x) = Finite x

    signum Infinity = Finite 1
    signum (Finite x) = Finite $ signum x

    fromInteger x = Finite $ fromInteger x

instance Ord x => Ord (Topped x) where
    compare (Finite _) Infinity = LT
    compare Infinity (Finite _) = GT
    compare Infinity Infinity = EQ
    compare (Finite x) (Finite y) = compare x y

class Forcable a where
    force :: a -> b -> b

instance Forcable a => Forcable [a] where
    force [] = id
    force (x:xs) = force x . force xs

instance Forcable x => Forcable (Topped x) where
    force Infinity = id
    force (Finite _) = id

instance Forcable AccessNr where
    force (AccessNr x) = force x

instance Forcable ThreadId where
    force (ThreadId x) = force x

instance Forcable Integer where
    force = seq

instance Forcable Int where
    force = seq

instance Forcable Word64 where
    force = seq

instance Forcable Word8 where
    force = seq

instance Forcable Bool where
    force = seq

instance Forcable x => Forcable (Maybe x) where
    force Nothing = id
    force (Just x) = force x

data DListEntry a = DListEntry {dle_prev :: Maybe (DListEntry a),
                                dle_next :: Maybe (DListEntry a),
                                dle_val :: a }

data DList a = DList { dle_head :: Maybe (DListEntry a),
                       dle_tail :: Maybe (DListEntry a) }

dlToList :: DList a -> [a]
dlToList dl = worker $ dle_head dl
              where worker Nothing = []
                    worker (Just x) = (dle_val x):(worker $ dle_next x)

listToDl :: [a] -> DList a
listToDl [] = DList Nothing Nothing
listToDl xs = let worker [] _ = (Nothing, Nothing)
                  worker (item:items) before =
                      let (nextEntry, lst) = worker items thisEntry
                          thisEntry = Just $ DListEntry { dle_prev = before,
                                                          dle_next = nextEntry,
                                                          dle_val = item }
                          lst' = case lst of
                                   Nothing -> thisEntry
                                   Just _ -> lst
                      in (thisEntry, lst')
                  (h, t) = worker xs Nothing
              in DList h t

dlLength :: DList a -> Int
dlLength = length . dlToList

instance Functor DList where
    fmap f x = listToDl $ fmap f $ dlToList x

instance Show a => Show (DList a) where
    show = show . dlToList

instance Read a => Read (DList a) where
    readsPrec _ x =
        do (v, trail) <- reads x
           return (listToDl v, trail)

instance Forcable a => Forcable (DListEntry a) where
    force dle val =
        force (dle_val dle) $
        force (dle_next dle) $
        case dle_prev dle of
          Nothing -> val
          Just p -> p `seq` val

instance Forcable a => Forcable (DList a) where
    force x y = force (dle_head x) $ case dle_tail x of
                                       Nothing -> y
                                       Just xt -> xt `seq` y

instance Eq a => Eq (DList a) where
    x == y = (dlToList x) == (dlToList y)

{- tid, (RIP, ptr) -}
type MemAccess = (ThreadId, (Word64, Word64))

{- A constraint a b means that a must happen before b -}
data SchedulingConstraint = SchedulingConstraint MemAccess MemAccess deriving Show

