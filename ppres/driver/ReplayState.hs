module ReplayState() where

import Types

instance Show ReplayState where
    show (ReplayStateOkay e) = "okay at " ++ (show e)
    show ReplayStateFinished = "finished"
    show (ReplayStateFailed s rn tid en r) = "failed: " ++ s ++ " (" ++ (show rn) ++ ", tid " ++ (show tid) ++ ", " ++ (show en) ++ ", reason " ++ (show r) ++ ")"
