module Types where

import Data.Word
import Network.Socket
import Numeric

type ThreadId = Integer
type VariableName = String

data HistoryEntry = HistoryRun (Topped Integer)
                  | HistoryRunThread ThreadId
                  | HistoryRunMemory ThreadId Integer
                    deriving (Eq, Show)

data History = History [HistoryEntry] deriving Show

data Worker = Worker { worker_fd :: Socket }

data TraceLocation = TraceLocation { trc_record :: Integer,
                                     trc_access :: Integer,
                                     trc_thread :: ThreadId } deriving Eq

instance Show TraceLocation where
    show tl = (show $ trc_record tl) ++ ":" ++ (show $ trc_access tl) ++ ":" ++ (show $ trc_thread tl)

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

data Expression = ExpressionRegister RegisterName Word64
                | ExpressionConst Word64
                | ExpressionMem Int TraceLocation Expression Expression
                | ExpressionImported Word64
                | ExpressionBinop Binop Expression Expression
                | ExpressionNot Expression

data ReplayFailureReason = FailureReasonControl Integer ThreadId deriving Show

data ReplayState = ReplayStateOkay
                 | ReplayStateFailed String ReplayFailureReason

data UIValue = UIValueNull
             | UIValueSnapshot History
             | UIValuePair UIValue UIValue
             | UIValueChar Char
             | UIValueList [UIValue]
             | UIValueTrace TraceRecord
             | UIValueError String
             | UIValueReplayState ReplayState
             | UIValueExpression Expression
             | UIValueByte Word8
             | UIValueInteger Integer
             | UIValueTraceLocation TraceLocation

data WorkerCache = WorkerCache { wc_workers :: [(History, Worker)],
                                 wc_start :: Worker }

data WorldState = WorldState { ws_bindings :: [(VariableName, UIValue)] }


instance Monad (Either a) where
    return x = Right x
    (Right x) >>= f = f x
    (Left x) >>= _ = Left x
    
data Topped x = Infinity
              | Finite x deriving Eq

instance Show x => Show (Topped x) where
    show Infinity = "{inf}"
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
