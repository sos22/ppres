module Classifier(mkBinaryClassifier,
                  classifierToExpression,
                  Classifier(..),
                  BooleanExpression(..)
    ) where

import Util
import Types

{- A classifier is essentially an n-ary classification key on
   (key,value) sets.  It's structured as a tree, where each node
   discriminates on one of the keys and the leaves represent final
   classifications. -}
data Classifier key value result = ClassifierLeaf result
                                 | ClassifierChoice key [(value, Classifier key value result)]
                                   deriving Show

{- Boolean expressions which can mention variables of type t -}
data BooleanExpression t = BooleanLeaf t
                         | BooleanConst Bool
                         | BooleanOr (BooleanExpression t) (BooleanExpression t)
                         | BooleanAnd (BooleanExpression t) (BooleanExpression t)
                         | BooleanNot (BooleanExpression t) deriving Show


data BooleanExpressionFolder s t =
    BooleanExpressionFolder { bef_leaf :: s -> t,
                              bef_const :: Bool -> t,
                              bef_or :: t -> t -> t,
                              bef_and :: t -> t -> t,
                              bef_not :: t -> t }

{- Build every possible classifier which is consistent with the list
   of samples and which doesn't just invent stuff out of thin air.
   The samples must be consistent, but they do not have to be
   complete.  If they are not complete, we'll take the nearest
   available result, for some vaguely sensible definition of
   nearest. -}
mkClassifier :: (Ord result, Ord key, Ord value) => [([(key,value)],result)] -> [(Classifier key value result)]
mkClassifier samples =
    let availresults = fastNub $ map snd samples
        allkeys = fastNub $ map fst $ concatMap fst samples
        valuesForKey k = fmap fastNub $ sequence $ map (lookup k . fst) samples
        availkeys = 
            {- A key must be present in every sample in order to be
               used as a discriminant, and must have multiple
               potential values. -}
            filter keyIsUsable allkeys
            where
              keyIsUsable k = case valuesForKey k of
                                Nothing -> False
                                Just [] -> error "Huh?"
                                Just [_] -> False
                                _ -> True
    in case availresults of
         [] -> []
         [x] -> return $ ClassifierLeaf x
         _ -> {- Multiple possible results, do it properly -}
              do discriminant <- availkeys
                 let fmaybe = maybe undefined id
                     flookup k kvs = fmaybe $ lookup k kvs
                     childForValue v =
                         mkClassifier [ ([kvs | kvs <- fst s, fst kvs /= discriminant], snd s)
                                        | s <- samples, flookup discriminant (fst s) == v]
                     clistEntryForValue v =
                         do c <- childForValue v
                            return (v, c)
                     children = sequence $ map clistEntryForValue $ fmaybe $ valuesForKey discriminant
                 c <- children
                 return $ ClassifierChoice discriminant c

mkBinaryClassifier :: (Ord key, Ord value) => [[(key,value)]] -> [[(key, value)]] -> [(Classifier key value Bool)]
mkBinaryClassifier true false =
    mkClassifier $ (zip true $ repeat True) ++ (zip false $ repeat False)


boolNot :: BooleanExpression t -> BooleanExpression t
boolNot (BooleanConst False) = BooleanConst True
boolNot (BooleanConst True) = BooleanConst False
boolNot x = BooleanNot x

boolAnd :: BooleanExpression t -> BooleanExpression t -> BooleanExpression t
boolAnd (BooleanConst False) _ = BooleanConst False
boolAnd (BooleanConst True) x = x
boolAnd _ (BooleanConst False) = BooleanConst False
boolAnd x (BooleanConst True) = x
boolAnd x y = BooleanAnd x y

boolOr :: BooleanExpression t -> BooleanExpression t -> BooleanExpression t
boolOr (BooleanConst False) x = x
boolOr (BooleanConst True) _ = BooleanConst True
boolOr x (BooleanConst False) = x
boolOr _ (BooleanConst True) = BooleanConst True
boolOr x y = BooleanOr x y

liftB :: t -> BooleanExpression t
liftB = BooleanLeaf

constB :: Bool -> BooleanExpression t
constB = BooleanConst

foldBooleanExpression :: BooleanExpressionFolder s t -> BooleanExpression s -> t
foldBooleanExpression f (BooleanLeaf s) = bef_leaf f s
foldBooleanExpression f (BooleanConst b) = bef_const f b
foldBooleanExpression f (BooleanOr l r) =
    bef_or f (foldBooleanExpression f l) (foldBooleanExpression f r)
foldBooleanExpression f (BooleanAnd l r) =
    bef_and f (foldBooleanExpression f l) (foldBooleanExpression f r)
foldBooleanExpression f (BooleanNot l) =
    bef_not f (foldBooleanExpression f l)

nopBefFolder :: BooleanExpressionFolder t (BooleanExpression t)
nopBefFolder = BooleanExpressionFolder { bef_leaf = liftB,
                                         bef_const = constB,
                                         bef_or = boolOr,
                                         bef_and = boolAnd,
                                         bef_not = boolNot }

classifierToExpression :: Classifier MemAccess (Maybe MemAccess) Bool -> BooleanExpression SchedulingConstraint
classifierToExpression (ClassifierLeaf r) = constB r
classifierToExpression (ClassifierChoice discriminant options) =
    let values = map fst options
        nullaryValue = boolNot $ foldr1 boolAnd [liftB $ SchedulingConstraint v discriminant | Just v <- values]
        exprForValue (v,c) =
            (case v of
               Nothing -> nullaryValue
               Just v' -> liftB $ SchedulingConstraint v' discriminant) `boolAnd`
            (classifierToExpression c)
        simplify = foldBooleanExpression $ nopBefFolder { bef_not = simplify_not }
                   where simplify_not (BooleanLeaf (SchedulingConstraint a b)) = BooleanLeaf $ SchedulingConstraint b a
                         simplify_not x = boolNot x
    in simplify $ foldr1 boolOr $ map exprForValue options


