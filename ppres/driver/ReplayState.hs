module ReplayState() where

import Types

instance Show ReplayState where
    show ReplayStateOkay = "okay"
    show (ReplayStateFailed s) = "failed: " ++ s
