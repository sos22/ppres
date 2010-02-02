module Expression() where

import Numeric

import Types

instance Show Binop where
    show BinopCombine = "comb"
    show BinopSub = "-"
    show BinopAdd = "+"
    show BinopMull = "*"
    show BinopMullHi = "*h"
    show BinopMullS = "*s"
    show BinopShrl = ">>>"
    show BinopShl = "<<"
    show BinopShra = ">>"
    show BinopAnd = "&"
    show BinopOr = "|"
    show BinopXor = "^"
    show BinopLe = "<=s"
    show BinopBe = "<="
    show BinopEq = "=="
    show BinopB = "<"

instance Show ExpressionCoord where
    show (ExpressionCoord rec acc) = "{" ++ (show rec) ++ "," ++ (show acc) ++ "}"

instance Show Expression where
    show (ExpressionRegister n val) = "(" ++ (show n) ++ ": " ++ (showHex val ")")
    show (ExpressionConst x) = showHex x ""
    show (ExpressionMem _ when ptr val) = "(" ++ (show when) ++ "MEM[" ++ (show ptr) ++ "]:" ++ (show val) ++ ")"
    show (ExpressionImported val) = "(imported:" ++ (showHex val ")")
    show (ExpressionBinop op l r) =
        "(" ++ (show l) ++ " " ++ (show op) ++ " " ++ (show r) ++ ")"
    show (ExpressionNot e) = "~(" ++ (show e) ++ ")"    
