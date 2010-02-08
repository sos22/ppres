{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Types where

import Data.Word
import Network.Socket
import Numeric
import Data.IORef

type ThreadId = Integer
type VariableName = String

newtype RecordNr = RecordNr Integer deriving (Eq, Show, Enum, Ord)
newtype EpochNr = EpochNr Integer deriving (Eq, Show, Enum, Ord, Real, Num)

data Worker = Worker { worker_fd :: Socket,
                       worker_alive :: IORef Bool }

data TraceLocation = TraceLocation { trc_epoch :: EpochNr,
                                     trc_record :: RecordNr,
                                     trc_access :: Integer,
                                     trc_thread :: ThreadId } deriving Eq

instance Show TraceLocation where
    show tl = (show $ trc_epoch tl) ++ ":" ++ (show $ trc_record tl) ++ ":" ++ (show $ trc_access tl) ++ ":" ++ (show $ trc_thread tl)

data TraceEntry = TraceFootstep { trc_foot_rip :: Word64,
                                  trc_foot_rdx :: Word64,
                                  trc_foot_rcx :: Word64,
                                  trc_foot_rax :: Word64 }
                | TraceSyscall { trc_sys_nr :: Int }
                | TraceRdtsc
                | TraceLoad { trc_load_val :: Word64,
                              trc_load_size :: Int,
                              trc_load_ptr :: Word64,
                              trc_load_in_monitor :: Bool }
                | TraceStore { trc_store_val :: Word64,
                               trc_store_size :: Int,
                               trc_store_ptr :: Word64,
                               trc_store_in_monitor :: Bool }
                | TraceCalling { trc_calling :: String }
                | TraceCalled { trc_called :: String }
                | TraceEnterMonitor
                | TraceExitMonitor

instance Show TraceEntry where
    show (TraceFootstep rip _ _ _ ) = "footstep " ++ (showHex rip "")
    show (TraceSyscall nr) = "syscall " ++ (show nr)
    show (TraceRdtsc) = "rdtsc"
    show (TraceLoad val _ ptr mon) =
        "load " ++ (showHex ptr $ " -> " ++ (showHex val (if mon then " (monitor)"
                                                          else "")))
    show (TraceStore val _ ptr mon) =
        "store " ++ (showHex ptr $ " -> " ++ (showHex val (if mon then " (monitor)"
                                                           else "")))
    show (TraceCalling c) = "calling " ++ c
    show (TraceCalled c) = "called " ++ c
    show TraceEnterMonitor = "enter monitor"
    show TraceExitMonitor = "exit monitor"

data TraceRecord = TraceRecord { trc_trc :: TraceEntry,
                                 trc_loc :: TraceLocation }

instance Show TraceRecord where
    show tr = (show $ trc_loc tr) ++ "\t" ++ (show $ trc_trc tr)

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
                    deriving Show

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
           | BinopB

instance Show Binop where
    show BinopCombine = "comb"
    show BinopSub = "-"
    show BinopAdd = "+"
    show BinopMull = "*"
    show BinopMullHi = "*h"
    show BinopMullS = "*s"
    show BinopShrl = ">>>"
    show BinopShl = "<<"
    show BinopShra = ">>"
    show BinopAnd = "&"
    show BinopOr = "|"
    show BinopXor = "^"
    show BinopLe = "<=s"
    show BinopBe = "<="
    show BinopEq = "=="
    show BinopB = "<"

data Expression = ExpressionRegister RegisterName Word64
                | ExpressionConst Word64
                | ExpressionMem Int TraceLocation Expression Expression
                | ExpressionImported Word64
                | ExpressionBinop Binop Expression Expression
                | ExpressionNot Expression

instance Show Expression where
    show (ExpressionRegister n val) = "(" ++ (show n) ++ ": " ++ (showHex val ")")
    show (ExpressionConst x) = showHex x ""
    show (ExpressionMem _ when ptr val) = "(" ++ (show when) ++ "MEM[" ++ (show ptr) ++ "]:" ++ (show val) ++ ")"
    show (ExpressionImported val) = "(imported:" ++ (showHex val ")")
    show (ExpressionBinop op l r) =
        "(" ++ (show l) ++ " " ++ (show op) ++ " " ++ (show r) ++ ")"
    show (ExpressionNot e) = "~(" ++ (show e) ++ ")"

data ReplayFailureReason = FailureReasonControl 
                         | FailureReasonData Expression Expression deriving Show

data ReplayState = ReplayStateOkay EpochNr
                 | ReplayStateFinished
                 | ReplayStateFailed String RecordNr ThreadId EpochNr ReplayFailureReason

data ThreadState = ThreadState { ts_dead :: Bool,
                                 ts_blocked :: Bool,
                                 ts_last_epoch :: EpochNr } deriving Show

instance Monad (Either a) where
    return x = Right x
    (Right x) >>= f = f x
    (Left x) >>= _ = Left x
    
data Topped x = Infinity
              | Finite x deriving Eq

instance Functor Topped where
    fmap _ Infinity = Infinity
    fmap f (Finite x) = Finite $ f x

instance Show x => Show (Topped x) where
    show Infinity = "inf"
    show (Finite x) = show x

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
    force (Finite x) = force x

instance Forcable EpochNr where
    force (EpochNr x) = force x

instance Forcable Integer where
    force = seq

instance Forcable Bool where
    force = seq
