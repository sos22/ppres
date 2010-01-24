module Types where

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

data UIValue = UIValueNull
             | UIValueSnapshot History
             | UIValuePair UIValue UIValue
             | UIValueString String
             | UIValueList [UIValue]
             | UIValueError String

data WorkerCache = WorkerCache { wc_workers :: [(History, Worker)],
                                 wc_start :: Worker }

data WorldState = WorldState { ws_bindings :: [(VariableName, UIValue)] }

type WorldMonad a = State WorldState a
