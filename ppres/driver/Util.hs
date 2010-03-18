module Util(first, second, deError, fastNub) where

import Data.List

first :: (a -> b) -> (a, c) -> (b, c)
first f (x, y) = (f x, y)

second :: (a -> b) -> (c, a) -> (c, b)
second f (x, y) = (x, f y)

deError :: Either String b -> b
deError (Right b) = b
deError (Left err) = error err

{- Like nub, but O(nlogn) rather than O(n^2), and only works on
   totally ordered values. -}
fastNub :: Ord a => [a] -> [a]
fastNub = map head . group . sort

