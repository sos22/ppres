module Util(first, second, deError) where

first :: (a -> b) -> (a, c) -> (b, c)
first f (x, y) = (f x, y)

second :: (a -> b) -> (c, a) -> (c, b)
second f (x, y) = (x, f y)

deError :: Either String b -> b
deError (Right b) = b
deError (Left err) = error err
