{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}

module Generic.Eval where

import Control.Monad (foldM)
import Data.Set qualified as Set
import Generic.Algebra

--- Evaluation:

-- Each element is a tuple (shound be homogenous)
data Result a where
  With :: (Set [a]) -> Result a
  Without :: (Set [a]) -> Result a
  deriving (Eq, Ord, Show)

resEmpty :: (Ord a) => Result a
resEmpty = With $ Set.empty

resUniv :: (Ord a) => Result a
resUniv = Without $ Set.empty

class Evaluateable t where
  eval :: (Ord a) => t a -> Maybe (Result a)

instance Evaluateable Finitary where
  eval (Finite x) = Just $ With $ Set.singleton [x]
  eval (Cofinite x) = Just $ Without $ Set.singleton [x]

instance Evaluateable Intersection where
  eval (Intersection xs) = foldr interRes resUniv <$> traverse eval xs

-- Without 2 x without 3 contains 1,2 1,3
-- Note: If _any_ of the products eval to 'Without', and none of them eval to
-- 'With empty', then the result is not finitary.
instance Evaluateable Times where
  eval (Times (x :| [])) = eval x
  eval (Times xs) = do
    y :| ys <- traverse eval xs
    foldM prodRes y ys

instance Evaluateable Union where
  eval (Union xs) = foldr unionRes resEmpty <$> traverse eval xs

complRes :: Result a -> Result a
complRes (With x) = Without x
complRes (Without x) = With x

interRes :: (Ord a) => Result a -> Result a -> Result a
With x `interRes` With y = With $ Set.intersection x y
With x `interRes` Without y = With $ x Set.\\ y
Without x `interRes` With y = With $ y Set.\\ x
Without x `interRes` Without y = Without $ Set.union x y

unionRes :: (Ord a) => Result a -> Result a -> Result a
With x `unionRes` With y = With $ Set.union x y
With x `unionRes` Without y = Without $ y Set.\\ x
Without x `unionRes` With y = Without $ x Set.\\ y
Without x `unionRes` Without y = Without $ Set.intersection x y

cartProd :: (Ord a) => Set [a] -> Set [a] -> Set [a]
xs `cartProd` ys = Set.cartesianProduct xs ys & Set.map (\(x, y) -> x <> y)

-- NOTE: When applying this, remember to check for any empty sets!
prodRes :: (Ord a) => Result a -> Result a -> Maybe (Result a)
With xs `prodRes` With ys
  | Set.null xs = Just resEmpty
  | Set.null ys = Just resEmpty
  | otherwise = Just $ With $ xs `cartProd` ys
Without _ `prodRes` _ = Nothing
_ `prodRes` Without _ = Nothing
