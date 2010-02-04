module ReplayState() where

import Types

instance Show ReplayState where
    show (ReplayStateOkay e) = "okay at " ++ (show e)
    show ReplayStateFinished = "finished"
    show (ReplayStateFailed s r) = "failed: " ++ s ++ " (" ++ (show r) ++ ")"
