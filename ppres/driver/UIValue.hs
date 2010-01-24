{-# LANGUAGE FlexibleInstances #-}
module UIValue(uiValueString, AvailInUI(..)) where

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

class AvailInUI a where
    toUI :: a -> UIValue
    fromUI :: UIValue -> Maybe a

instance AvailInUI () where
    toUI () = UIValueNull
    fromUI UIValueNull = Just ()
    fromUI _ = Nothing

instance AvailInUI History where
    toUI = UIValueSnapshot
    fromUI (UIValueSnapshot x) = Just x
    fromUI _ = Nothing

instance (AvailInUI a, AvailInUI b) => AvailInUI (a, b) where
    toUI (a, b) = UIValuePair (toUI a) (toUI b)
    fromUI (UIValuePair a b) =
        do a' <- fromUI a
           b' <- fromUI b
           return $ (a', b')
    fromUI _ = Nothing

instance AvailInUI TraceRecord where
    toUI = UIValueTrace
    fromUI (UIValueTrace t) = Just t
    fromUI _ = Nothing

instance AvailInUI a => AvailInUI [a] where
    toUI = UIValueList . (map toUI)
    fromUI (UIValueList t) = mapM fromUI t
    fromUI _ = Nothing

instance AvailInUI a => AvailInUI (Either String a) where
    toUI (Left err) = UIValueError err
    toUI (Right x) = toUI x
    fromUI (UIValueError e) = Just $ Left e
    fromUI x = fmap Right $ fromUI x

instance AvailInUI a => AvailInUI (Maybe a) where
    toUI Nothing = UIValueNull
    toUI (Just x) = toUI x
    fromUI (UIValueNull) = Just Nothing
    fromUI x = fmap Just $ fromUI x

instance AvailInUI Char where
    toUI = UIValueChar
    fromUI (UIValueChar c) = Just c
    fromUI _ = Nothing
