module UIValue() where

import Types

instance Show UIValue where
    show UIValueNull = "()"
    show (UIValueSnapshot _) = "<snapshot>"
