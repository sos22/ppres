module Types where

import Data.Word
import Network.Socket
import Control.Monad.State

type ThreadId = Integer
type VariableName = String

data HistoryEntry = HistoryRun Integer
                  | HistoryRunThread ThreadId
                  | HistoryRunMemory ThreadId Integer
                    deriving (Eq, Show)

data History = History [HistoryEntry] deriving Show

data Worker = Worker { worker_fd :: Socket }

data TraceLocation = TraceLocation { trc_record :: Integer,
                                     trc_access :: Integer,
                                     trc_thread :: ThreadId } deriving Show
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
                | TraceExitMonitor deriving Show

data TraceRecord = TraceRecord { trc_trc :: TraceEntry,
                                 trc_loc :: TraceLocation } deriving Show

data UIValue = UIValueNull
             | UIValueSnapshot History
             | UIValuePair UIValue UIValue
             | UIValueString String
             | UIValueList [UIValue]
             | UIValueTrace TraceRecord
             | UIValueError String

data WorkerCache = WorkerCache { wc_workers :: [(History, Worker)],
                                 wc_start :: Worker }

data WorldState = WorldState { ws_bindings :: [(VariableName, UIValue)] }

type WorldMonad a = State WorldState a
