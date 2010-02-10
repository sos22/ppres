{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Types where

import Data.Word
import Network.Socket
import Numeric
import Data.IORef

import Util

type ThreadId = Integer
type VariableName = String

newtype RecordNr = RecordNr Integer deriving (Eq, Show, Enum, Ord, Read)
newtype EpochNr = EpochNr Integer deriving (Eq, Show, Enum, Ord, Real, Num, Read)

data Worker = Worker { worker_fd :: Socket,
                       worker_alive :: IORef Bool }

data TraceLocation = TraceLocation { trc_epoch :: EpochNr,
                                     trc_record :: RecordNr,
                                     trc_access :: Integer,
                                     trc_thread :: ThreadId } deriving Eq

instance Show TraceLocation where
    show tl = (show $ trc_epoch tl) ++ ":" ++ (show $ trc_record tl) ++ ":" ++ (show $ trc_access tl) ++ ":" ++ (show $ trc_thread tl)

instance Read TraceLocation where
    readsPrec _ x =
        let readChar _ [] = []
            readChar c (c':o) = if c == c' then [o]
                                else []
        in
        do (epoch,trail1) <- reads x
           trail2 <- readChar ':' trail1
           (record,trail3) <- reads trail2
           trail4 <- readChar ':' trail3
           (access,trail5) <- reads trail4
           trail6 <- readChar ':' trail5
           (thread,trail7) <- reads trail6
           return (TraceLocation epoch record access thread, trail7)
                              
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
        "load " ++ (showHex ptr $ " -> " ++ (showHex val (if mon then " monitor"
                                                          else "")))
    show (TraceStore val _ ptr mon) =
        "store " ++ (showHex ptr $ " -> " ++ (showHex val (if mon then " monitor"
                                                           else "")))
    show (TraceCalling c) = "calling " ++ c
    show (TraceCalled c) = "called " ++ c
    show TraceEnterMonitor = "enter_monitor"
    show TraceExitMonitor = "exit_monitor"

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
                                 then return (c val 0 ptr True, trail5)
                                 else return (c val 0 ptr False, trail4)
             _ -> []

data TraceRecord = TraceRecord { trc_trc :: TraceEntry,
                                 trc_loc :: TraceLocation } deriving (Show, Read)

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
                    deriving (Show, Read)

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
                | ExpressionMem Int TraceLocation Expression Expression
                | ExpressionImported Word64
                | ExpressionBinop Binop Expression Expression
                | ExpressionNot Expression deriving (Show, Read)

data ReplayFailureReason = FailureReasonControl 
                         | FailureReasonData Expression Expression deriving (Show, Read)

data ReplayState = ReplayStateOkay EpochNr
                 | ReplayStateFinished
                 | ReplayStateFailed String RecordNr ThreadId EpochNr ReplayFailureReason deriving (Show, Read)

data ThreadState = ThreadState { ts_dead :: Bool,
                                 ts_blocked :: Bool,
                                 ts_last_epoch :: EpochNr,
                                 ts_last_rip :: Word64 } deriving Show

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

instance Read x => Read (Topped x) where
    readsPrec _ ('i':'n':'f':x) = [(Infinity, x)]
    readsPrec _ x = map (first Finite) $ reads x

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
