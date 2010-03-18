{-# LANGUAGE FlexibleInstances #-}
module UIValue(uiValueString, AvailInUI(..), mapUIValue, UIValue(..), uiApply,
               uiValueEq) where

import Control.Monad.Instances()
import Control.Monad
import Data.Word
import Numeric
import Char

import Types
import ReplayState()
import History
import Util
import Classifier

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
             | UIValueReplayCoord AccessNr
             | UIValueThreadState ThreadState
             | UIValueRegisterName RegisterName
             | UIValueWord Word64
             | UIValueFunction (UIValue -> UIValue)
             | UIValueThreadId ThreadId
             | UIValueBool Bool
             | UIValueClassifier (Classifier (ThreadId, (Word64, Word64)) (Maybe (ThreadId, (Word64, Word64))) Bool)
             | UIValueClassExpr (BooleanExpression SchedulingConstraint)

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
    show (UIValueReplayCoord tr) = "{" ++ (show tr) ++ "}"
    show (UIValueThreadState ts) = show ts
    show (UIValueRegisterName x) = show x
    show (UIValueWord x) = "WORD 0x" ++ (showHex x "")
    show (UIValueFunction _) = "FUNC"
    show (UIValueThreadId (ThreadId t)) = "~" ++ (show t)
    show (UIValueBool True) = "True"
    show (UIValueBool False) = "False"
    show (UIValueClassifier c) = show c
    show (UIValueClassExpr c) = show c

simpleWrappedReadsPrec :: (Read a) => (a -> t) -> String -> [(t, String)] -> [(t, String)]
simpleWrappedReadsPrec constructor t continuation =
    case (do (contents, trail1) <- reads t
             case trail1 of
               '}':trail2 -> return (constructor contents, trail2)
               _ -> []) of
      [] -> continuation
      x -> x

instance Read UIValue where
    readsPrec _ [] = []
    readsPrec _ ('(':')':x) = [(UIValueNull,x)]
    readsPrec _ ('(':t) =
        do (left, trail1) <- reads t
           case trail1 of
             ',':' ':trail2 ->
                 do (right, trail3) <- reads trail2
                    case trail3 of
                      ')':trail4 -> return (UIValuePair left right, trail4)
                      _ -> []
             _ -> []
    readsPrec _ x | isDigit (head x) = map (first UIValueInteger) $ reads x
    readsPrec _ ('{':t) = simpleWrappedReadsPrec UIValueReplayCoord t $
                          simpleWrappedReadsPrec UIValueRegisterName t $
                          []
    readsPrec _ ('[':t) =
        let readListBody tt =
                ([], tt):
                       (do (item, trail2) <- reads tt
                           case trail2 of
                             '\n':trail3 ->
                                 do (rest,trail4) <- readListBody trail3
                                    return (item:rest,trail4)
                             _ -> [])
        in
          do (contents, trail1) <- readListBody t
             case trail1 of
               ']':trail2 -> return (UIValueList contents, trail2)
               _ -> []
    readsPrec _ ('~':trail) =
        do (v, trail2) <- reads trail
           return (UIValueThreadId $ ThreadId v, trail2)
    readsPrec _ x = do (keyword, trail1) <- lex x
                       case keyword of
                         "ERR" -> return (UIValueError trail1, [])
                         "TRC" -> do (v, trail2) <- reads trail1
                                     return (UIValueTrace v, trail2)
                         "RS" -> do (v, trail2) <- reads trail1
                                    return (UIValueReplayState v, trail2)
                         "EXPR" -> do (v, trail2) <- reads trail1
                                      return (UIValueExpression v, trail2)
                         "BYTE" -> do (v, trail2) <- reads trail1
                                      return (UIValueByte v, trail2)
                         "WORD" -> do (v, trail2) <- reads trail1
                                      return (UIValueWord v, trail2)
                         "History" -> do (v, trail2) <- reads x
                                         return (UIValueSnapshot v, trail2)
                         "FUNC" -> [(UIValueError "can't parse functions", trail1)]
                         "True" -> return (UIValueBool True, trail1)
                         "False" -> return (UIValueBool False, trail1)
                         _ -> []

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

uiApply :: UIValue -> UIValue -> UIValue
uiApply f a =
    case fromUI f of
      Left e -> UIValueError e
      Right f' -> f' a

uiValueEq :: UIValue -> UIValue -> Either String Bool
uiValueEq UIValueNull UIValueNull = Right True
uiValueEq (UIValueSnapshot h) (UIValueSnapshot h') = Right $ h == h'
uiValueEq (UIValuePair a b) (UIValuePair c d) =
    do x <- uiValueEq a c
       y <- uiValueEq b d
       return $ x && y
uiValueEq (UIValueChar x) (UIValueChar y) = Right $ x == y
uiValueEq (UIValueList xs) (UIValueList ys) =
    worker xs ys
    where worker [] [] = Right True
          worker (a:as) (b:bs) = do x <- uiValueEq a b
                                    y <- worker as bs
                                    return $ x && y
          worker _ _ = Right False
uiValueEq (UIValueTrace x) (UIValueTrace y) = Right $ x == y
uiValueEq (UIValueReplayState _) (UIValueReplayState _) =
    Left "equality not defined over replay states"
uiValueEq (UIValueExpression _) (UIValueExpression _) =
    Left "equality not defined over expressions"
uiValueEq (UIValueByte b) (UIValueByte b') = Right $ b == b'
uiValueEq (UIValueInteger x) (UIValueInteger y) = Right $ x == y
uiValueEq (UIValueReplayCoord x) (UIValueReplayCoord y) = Right $ x == y
uiValueEq (UIValueThreadState x) (UIValueThreadState y) = Right $ x == y
uiValueEq (UIValueRegisterName x) (UIValueRegisterName y) = Right $ x == y
uiValueEq (UIValueWord x) (UIValueWord y) = Right $ x == y
uiValueEq (UIValueFunction _) (UIValueFunction _) =
    Left "equality not defined over functions"
uiValueEq (UIValueThreadId x) (UIValueThreadId y) = Right $ x == y
uiValueEq (UIValueBool x) (UIValueBool y) = Right $ x == y
uiValueEq _ _ = Right False

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

instance AvailInUI Integer where
    toUI = UIValueInteger
    fromUI (UIValueInteger i) = Right i
    fromUI e = coerceError "integer" e

instance AvailInUI ThreadState where
    toUI = UIValueThreadState
    fromUI (UIValueThreadState i) = Right i
    fromUI e = coerceError "thread state" e

instance AvailInUI RegisterFile where
    toUI (RegisterFile x) = toUI x
    fromUI = fmap RegisterFile . fromUI

instance AvailInUI RegisterName where
    toUI = UIValueRegisterName
    fromUI (UIValueRegisterName x) = Right x
    fromUI e = coerceError "register name" e

instance AvailInUI Word64 where
    toUI = UIValueWord
    fromUI (UIValueWord x) = Right x
    fromUI e = coerceError "word" e

instance AvailInUI CriticalSection where
    toUI (CriticalSection t x) = toUI (t, x)
    fromUI x = do (t, v) <- fromUI x
                  return $ CriticalSection t v

instance AvailInUI (UIValue -> UIValue) where
    toUI = UIValueFunction
    fromUI (UIValueFunction f) = Right f
    fromUI x = coerceError "function" x

instance AvailInUI UIValue where
    toUI = id
    fromUI x = case x of
                 UIValueError e -> Left e
                 _ -> Right x

instance AvailInUI Int where
    toUI = UIValueInteger . toInteger
    fromUI (UIValueInteger v) =
        if v < toInteger (minBound :: Int) ||
           v > toInteger (maxBound :: Int)
        then Left $ (show v) ++ " is out of range for an Int"
        else Right $ fromInteger v
    fromUI e = coerceError "Int" e

instance AvailInUI ThreadId where
    toUI = UIValueThreadId
    fromUI (UIValueThreadId tid) = Right tid
    fromUI e = coerceError "ThreadId" e

instance AvailInUI AccessNr where
    toUI = UIValueReplayCoord
    fromUI (UIValueReplayCoord e) = Right e
    fromUI e = coerceError "ReplayCoord" e

instance AvailInUI Bool where
    toUI = UIValueBool
    fromUI (UIValueBool e) = Right e
    fromUI e = coerceError "Bool" e

instance AvailInUI (Classifier (ThreadId, (Word64, Word64)) (Maybe (ThreadId, (Word64, Word64))) Bool) where
    toUI = UIValueClassifier 
    fromUI (UIValueClassifier c) = Right c
    fromUI e = coerceError "classifier" e

instance AvailInUI (BooleanExpression SchedulingConstraint) where
    toUI = UIValueClassExpr
    fromUI (UIValueClassExpr e) = Right e
    fromUI e = coerceError "ClassifierExpression" e

instance AvailInUI a => AvailInUI (Topped a) where
    toUI Infinity = UIValueNull
    toUI (Finite x) = toUI x
    fromUI UIValueNull = Right Infinity
    fromUI x = fmap Finite $ fromUI x