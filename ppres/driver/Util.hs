module Util(first) where

first :: (a -> b) -> (a, c) -> (b, c)
first f (x, y) = (f x, y)
