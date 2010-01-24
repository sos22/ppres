module UIValue(uiValueString) where

import Types

instance Show UIValue where
    show UIValueNull = "()"
    show (UIValueSnapshot s) = show s
    show (UIValuePair a b) = "(" ++ (show a) ++ ", " ++ (show b) ++ ")"
    show (UIValueList a) =
        let isChar (UIValueChar _) = True
            isChar _ = False
            gChar (UIValueChar c) = c
            gChar _ = error "Huh?"
        in if and $ map isChar a
           then map gChar a
           else "[" ++ (foldr (\x y -> x ++ "\n" ++ y) "]" $ map show a)
    show (UIValueChar c) = c:[]
    show (UIValueError e) = "ERR " ++ e
    show (UIValueTrace t) = "TRC " ++ show t

uiValueString :: String -> UIValue
uiValueString s = UIValueList $ map UIValueChar s