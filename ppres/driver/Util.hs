module Util(first, deError) where

first :: (a -> b) -> (a, c) -> (b, c)
first f (x, y) = (f x, y)

deError :: Either String b -> b
deError (Right b) = b
deError (Left err) = error err
