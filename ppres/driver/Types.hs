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

data WorldState = WorldState { ws_bindings :: [(VariableName, UIValue)],
                               ws_workers :: [(History, Worker)],
                               ws_starting_worker :: Worker }

type WorldMonad a = StateT WorldState IO a
