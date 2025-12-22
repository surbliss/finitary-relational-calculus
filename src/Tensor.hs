{-# LANGUAGE GHC2024 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Tensor where

import Data.Set (Set, intersection, union, unions, (\\))
import Data.Set qualified as Set
import Data.Vector.Sized (Vector)
import Data.Vector.Sized qualified as Vec
import GHC.TypeLits

---------------------------------------------------
-- Datatypes
---------------------------------------------------
-- One-dim algebra
data Finitary a where
  Finite :: a -> Finitary a
  Cofinite :: a -> Finitary a
  Empty :: Finitary a
  Univ :: Finitary a
  (:/\) :: Finitary a -> Finitary a -> Finitary a -- Intersection
  (:\/) :: Finitary a -> Finitary a -> Finitary a -- Union

type Product (n :: Nat) a = Vector n (Finitary a)

-- Note: List empty shold be same thing as product of Empties
data TensorTerm (n :: Nat) a where
  Term :: [Product n a] -> TensorTerm n a

-- Intersections only allowed in each factor of product

infixr 5 :\/
infixr 6 :/\

deriving instance (Show a) => Show (Finitary a)

---------------------------------------------------
-- Type classes and implementations
---------------------------------------------------
class SetAlgebra a where
  univ :: a
  empty :: a
  (\/) :: a -> a -> a
  (/\) :: a -> a -> a
  compl :: a -> a

instance SetAlgebra (Finitary a) where
  univ = Univ

  empty = Empty

  -- Clean out identity-terms for union and intersection
  Empty \/ x = x
  x \/ Empty = x
  Univ \/ _ = Univ
  _ \/ Univ = Univ
  x \/ y = x :\/ y

  -- QUESTION: Should /\ be moved further in than \/?
  Univ /\ x = x
  x /\ Univ = x
  Empty /\ _ = Empty
  _ /\ Empty = Empty
  x /\ y = x :/\ y

  compl (Finite s) = Cofinite s
  compl (Cofinite s) = Cofinite s
  compl Empty = Univ
  compl Univ = Empty
  compl (x :\/ y) = compl x /\ compl y
  compl (x :/\ y) = compl x \/ compl y

instance (KnownNat n) => SetAlgebra (TensorTerm n a) where
  univ = Term [Vec.replicate Univ]
  empty = Term []

  Term xs \/ Term ys = Term (xs ++ ys)

  Term [] /\ Term _ = Term []
  Term _ /\ Term [] = Term []
  Term [x] /\ Term [y] = Term [prodIntersect x y]
    where
      prodIntersect ps qs = Vec.zipWith (/\) ps qs

  compl x = undefined

(><) :: Product n a -> Product m a -> Product (n + m) a
x >< y = x Vec.++ y
