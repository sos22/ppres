{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Types where

import Debug.Trace

import Data.Word
import Network.Socket
import Numeric
import Data.IORef

import Util

type ThreadId = Integer
type VariableName = String

newtype RecordNr = RecordNr Integer deriving (Eq, Show, Enum, Ord, Read)
newtype EpochNr = EpochNr Integer deriving (Eq, Show, Enum, Ord, Real, Num, Read, Integral)
newtype AccessNr = AccessNr Integer deriving (Eq, Show, Enum, Ord, Real, Num, Read, Integral)

data Worker = Worker { worker_fd :: Socket,
                       worker_alive :: IORef Bool }

instance Show Worker where
    show w = "worker fd " ++ (show $ worker_fd w)

data ReplayCoord = ReplayCoord { rc_epoch :: EpochNr,
                                 rc_access :: AccessNr } deriving (Eq)

instance Ord ReplayCoord where
    compare a b =
        if rc_epoch a < rc_epoch b
        then LT
        else if rc_epoch a == rc_epoch b
             then rc_access a `compare` rc_access b
             else GT

startCoord :: ReplayCoord
startCoord = ReplayCoord 0 0

instance Show ReplayCoord where
    show tl = (show $ rc_epoch tl) ++ ":" ++ (show $ rc_access tl)

instance Read ReplayCoord where
    readsPrec _ x =
        let readChar _ [] = []
            readChar c (c':o) = if c == c' then [o]
                                else []
        in
        do (epoch,trail1) <- reads x
           trail2 <- readChar ':' trail1
           (access,trail3) <- reads trail2
           return (ReplayCoord epoch access, trail3)
                              
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
                                 trc_loc :: ReplayCoord } deriving (Show, Read)

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
                | ExpressionMem Int ReplayCoord Expression Expression
                | ExpressionImported Word64
                | ExpressionBinop Binop Expression Expression
                | ExpressionNot Expression deriving (Show, Read)

data ReplayFailureReason = FailureReasonControl 
                         | FailureReasonData Expression Expression deriving (Show, Read)

data ReplayState = ReplayStateOkay ReplayCoord
                 | ReplayStateFinished
                 | ReplayStateFailed String ThreadId ReplayCoord ReplayFailureReason deriving (Show, Read)

data ThreadState = ThreadState { ts_dead :: Bool,
                                 ts_blocked :: Bool,
                                 ts_last_run :: ReplayCoord,
                                 ts_last_rip :: Word64 } deriving Show

instance Monad (Either a) where
    return x = Right x
    (Right x) >>= f = f x
    (Left x) >>= _ = Left x
    
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

instance Forcable EpochNr where
    force (EpochNr x) = force x

instance Forcable AccessNr where
    force (AccessNr x) = force x

instance Forcable Integer where
    force = seq

instance Forcable Int where
    force = seq

instance Forcable Bool where
    force = seq

instance Forcable x => Forcable (Maybe x) where
    force Nothing = id
    force (Just x) = force x

instance Forcable ReplayCoord where
    force rc = (force $ rc_epoch rc) . (force $ rc_access rc)

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
