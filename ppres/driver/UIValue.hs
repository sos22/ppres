module UIValue(uiv_destruct) where

import Types
import Worker

instance Show UIValue where
    show UIValueNull = "()"
    show (UIValueSnapshot _) = "<snapshot>"

uiv_destruct :: UIValue -> WorldMonad ()
uiv_destruct UIValueNull = return ()
uiv_destruct (UIValueSnapshot s) = killWorker s >> return ()
