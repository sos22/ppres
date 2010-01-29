module Expression() where

import Numeric

import Types

binopPrec :: Binop -> Int
binopPrec BinopCombine = 1
binopPrec BinopSub = 2
binopPrec BinopAdd = 3
binopPrec BinopMull = 4
binopPrec BinopMullHi = 4
binopPrec BinopMullS = 4
binopPrec BinopShrl = 5
binopPrec BinopShl = 6
binopPrec BinopShra = 7
binopPrec BinopAnd = 8
binopPrec BinopXor = 8
binopPrec BinopOr = 8
binopPrec BinopLe = 9
binopPrec BinopBe = 9
binopPrec BinopEq = 9
binopPrec BinopB = 9

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
