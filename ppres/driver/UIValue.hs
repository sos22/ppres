module UIValue(uiv_destruct) where

import Types

instance Show UIValue where
    show UIValueNull = "()"
    show (UIValueSnapshot _) = "<snapshot>"

uiv_destruct :: UIValue -> WorldMonad ()
uiv_destruct _ = return ()
