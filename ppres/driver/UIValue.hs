module UIValue() where

import Types

instance Show UIValue where
    show UIValueNull = "()"
    show (UIValueSnapshot s) = show s
    show (UIValuePair a b) = "(" ++ (show a) ++ ", " ++ (show b) ++ ")"
    show (UIValueList a) = "[" ++ (foldr (\x y -> x ++ ", " ++ y) "]" $ map show a)
    show (UIValueString s) = s
    show (UIValueError e) = "ERR " ++ e
