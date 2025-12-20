{-# LANGUAGE GHC2024 #-}

module Finitary where

import Data.Set
import Prelude hiding (empty, fromList)

-- Left = Cofinite, Right = Finite
data Finitary a where
  Finite :: Set a -> Finitary a
  Cofinite :: Set a -> Finitary a
  deriving stock (Eq, Ord, Show)

data Algebra a where
  Base :: Finitary a -> Algebra a
  (:+) :: Algebra a -> Algebra a -> Algebra a
  (:*) :: Algebra a -> Algebra a -> Algebra a
  C :: Algebra a -> Algebra a
  deriving stock (Eq, Ord, Show)

data Tensor a where
  Single :: Algebra a -> Tensor a
  Product :: [Algebra a] -> Tensor a

alg :: (Ord a) => [a] -> Algebra a
alg xs = Base $ Finite $ fromList xs

emptySet :: Finitary a
emptySet = Finite empty

univSet :: Finitary a
univSet = Cofinite empty

fCompl :: Finitary a -> Finitary a
fCompl (Finite s) = Cofinite s
fCompl (Cofinite s) = Finite s

fUnion :: (Ord a) => Finitary a -> Finitary a -> Finitary a
fUnion (Finite s) (Finite t) = Finite (s `union` t)
fUnion (Finite s) (Cofinite t) = Cofinite (t \\ s)
fUnion (Cofinite s) (Finite t) = Cofinite (s \\ t)
fUnion (Cofinite s) (Cofinite t) = Cofinite (s `intersection` t)

fIntersection :: (Ord a) => Finitary a -> Finitary a -> Finitary a
fIntersection (Finite s) (Finite t) = Finite (s `intersection` t)
fIntersection (Finite s) (Cofinite t) = Finite (s \\ t)
fIntersection (Cofinite s) (Finite t) = Finite (t \\ s)
fIntersection (Cofinite s) (Cofinite t) = Cofinite (s `union` t)

eval :: (Ord a) => Algebra a -> Finitary a
eval (Base s) = s
eval (x :+ y) = eval x `fUnion` eval y
eval (x :* y) = eval x `fIntersection` eval y
eval (C x) = fCompl $ eval x

-- compl :: Algebra a -> Algebra a
-- compl Empty = Univ
-- compl Univ = Empty
-- compl (Finite s) = Cofinite s
-- compl (Cofinite s) = Finite s
-- compl (x :+ y) = compl x :* compl y
-- compl (x :* y) = compl x :* compl y

-- eval :: Algebra (Set a) -> Finitary a
-- eval Empty = Right S.empty
-- eval Univ = Left S.empty
-- eval (Finite s) = Right s
-- eval (Cofinite s) = Left s
-- -- eval (Finite s :+ Finite s)
-- eval _ = undefined

-- (%+) :: Algebra a -> Algebra a -> Algebra a
-- Empty %+ x = x
-- x %+ Empty = x
-- C x %+ C y = compl (x %* y)
-- x %+ y = x :+ y

-- -- Intersections should be moved in, and unions out?
-- (%*) :: Algebra a -> Algebra a -> Algebra a
-- Empty %* _ = Empty
-- _ %* Empty = Empty
-- C x %* C y = compl (x %+ y)
-- x %* y = x :* y

-- simplify :: Algebra a -> Algebra a
-- simplify Empty = Empty
-- simplify (Base x) = Base x
-- simplify (x :+ y) = simplify x %+ simplify y
-- simplify (x :* y) = simplify x %* simplify y
-- simplify (C x) = compl x

-- eval :: Algebra (Set a) -> Finitary (Set a)
-- eval = eval' True . simplify

-- ifFinitary :: Bool -> a -> Finitary a
-- ifFinitary True a = Finite a
-- ifFinitary False a = Cofinite a

-- eval' :: Bool -> Algebra (Set a) -> Finitary (Set a)
-- eval' b Empty = ifFinitary b S.empty
-- eval' b (Base s) = ifFinitary b s
-- eval' b (C x) = eval' (not b) x
-- eval' b (x :+ y) = union
-- -- eval' (Base x) = Finite x
-- -- eval' (Base (Cofinite x)) = Nothing
-- eval' _ _ = undefined
