{-# LANGUAGE FlexibleInstances #-}
module UIValue(uiValueString, AvailInUI(..), mapUIValue, UIValue(..)) where

import Control.Monad.Instances()
import Control.Monad
import Data.Word
import Numeric

import Types
import ReplayState()
import History

data UIValue = UIValueNull
             | UIValueSnapshot History
             | UIValuePair UIValue UIValue
             | UIValueChar Char
             | UIValueList [UIValue]
             | UIValueTrace TraceRecord
             | UIValueError String
             | UIValueReplayState ReplayState
             | UIValueExpression Expression
             | UIValueByte Word8
             | UIValueInteger Integer
             | UIValueTraceLocation TraceLocation
             | UIValueThreadState ThreadState
             | UIValueHistoryDiff HistoryDiff

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
    show (UIValueReplayState rs) = "RS " ++ show rs
    show (UIValueExpression e) = "EXPR " ++ (show e)
    show (UIValueByte b) = "BYTE 0x" ++ (showHex b "")
    show (UIValueInteger r) = "0x" ++ (showHex r "")
    show (UIValueTraceLocation tr) = "{" ++ (show tr) ++ "}"
    show (UIValueThreadState ts) = show ts
    show (UIValueHistoryDiff hd) = show hd

uiValueString :: String -> UIValue
uiValueString s = UIValueList $ map UIValueChar s

class AvailInUI a where
    toUI :: a -> UIValue
    fromUI :: UIValue -> Either String a

coerceError :: String -> UIValue -> Either String a
coerceError wanted got = Left $ "Type error: wanted " ++ wanted ++ ", got " ++ (show got)

mapUIValue :: (AvailInUI a, AvailInUI b) => (a -> b) -> UIValue -> UIValue
mapUIValue f b =
    toUI $ liftM f $ fromUI b

instance AvailInUI () where
    toUI () = UIValueNull
    fromUI UIValueNull = Right ()
    fromUI e = coerceError "()" e

instance AvailInUI History where
    toUI = UIValueSnapshot
    fromUI (UIValueSnapshot x) = Right x
    fromUI x = coerceError "snapshot" x

instance (AvailInUI a, AvailInUI b) => AvailInUI (a, b) where
    toUI (a, b) = UIValuePair (toUI a) (toUI b)
    fromUI (UIValuePair a b) =
        do a' <- fromUI a
           b' <- fromUI b
           return $ (a', b')
    fromUI e = coerceError "pair" e

instance AvailInUI TraceRecord where
    toUI = UIValueTrace
    fromUI (UIValueTrace t) = Right t
    fromUI e = coerceError "trace record" e

instance AvailInUI a => AvailInUI [a] where
    toUI = UIValueList . (map toUI)
    fromUI (UIValueList t) = mapM fromUI t
    fromUI e = coerceError "list" e

instance AvailInUI a => AvailInUI (Either String a) where
    toUI (Left err) = UIValueError err
    toUI (Right x) = toUI x
    fromUI (UIValueError e) = Right $ Left e
    fromUI x = fmap Right $ fromUI x

instance AvailInUI a => AvailInUI (Maybe a) where
    toUI Nothing = UIValueNull
    toUI (Just x) = toUI x
    fromUI (UIValueNull) = Right Nothing
    fromUI x = fmap Just $ fromUI x

instance AvailInUI Char where
    toUI = UIValueChar
    fromUI (UIValueChar c) = Right c
    fromUI e = coerceError "char" e

instance AvailInUI ReplayState where
    toUI = UIValueReplayState
    fromUI (UIValueReplayState s) = Right s
    fromUI e = coerceError "replay state" e

instance AvailInUI Expression where
    toUI = UIValueExpression
    fromUI (UIValueExpression e) = Right e
    fromUI e = coerceError "expression" e

instance AvailInUI Word8 where
    toUI = UIValueByte
    fromUI (UIValueByte b) = Right b
    fromUI e = coerceError "byte" e

instance AvailInUI TraceLocation where
    toUI = UIValueTraceLocation
    fromUI (UIValueTraceLocation l) = Right l
    fromUI e = coerceError "trace location" e

instance AvailInUI Integer where
    toUI = UIValueInteger
    fromUI (UIValueInteger i) = Right i
    fromUI e = coerceError "integer" e

instance AvailInUI ThreadState where
    toUI = UIValueThreadState
    fromUI (UIValueThreadState i) = Right i
    fromUI e = coerceError "thread state" e

instance AvailInUI HistoryDiff where
    toUI = UIValueHistoryDiff
    fromUI (UIValueHistoryDiff i) = Right i
    fromUI e = coerceError "history diff" e