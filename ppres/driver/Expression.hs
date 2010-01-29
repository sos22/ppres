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
    showsPrec p (ExpressionRegister n val) =
        showParen (p <= 11) $ shows n . showHex val
    showsPrec _ (ExpressionConst x) = showHex x
    showsPrec p (ExpressionMem _ when ptr val) =
        showParen (p <= 11) $ shows when . showString "[" . showsPrec 0 ptr . showString "]" . showsPrec 11 val
    showsPrec _ (ExpressionImported) = showString "imported"
    showsPrec p (ExpressionBinop op l r) =
        let prec = binopPrec op
        in showParen (p <= prec) $ showsPrec prec l . showString " " . shows op . showString " " . showsPrec prec r
    showsPrec p (ExpressionNot e) =
        showParen (p <= 1) $ showString "~" . showsPrec 2 e
    