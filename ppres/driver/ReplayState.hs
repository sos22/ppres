module ReplayState() where

import Types

instance Show ReplayState where
    show ReplayStateOkay = "okay"
    show ReplayStateFinished = "finished"
    show (ReplayStateFailed s r) = "failed: " ++ s ++ " (" ++ (show r) ++ ")"
