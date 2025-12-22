{-# LANGUAGE GHC2024 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Finitary where

import Data.Set (Set, intersection, union, unions, (\\))
import Data.Set qualified as Set
import Data.Vector.Sized (Vector)
import Data.Vector.Sized qualified as Vec
import GHC.TypeLits

---------------------------------------------------
-- Datatypes
---------------------------------------------------

-- Int?
type Permutation = [Nat]

data FOL (n :: Nat) a where
  -- Cross product of
  Predicate :: [Set a] -> FOL n a -- length list = n
  And :: FOL n a -> FOL n a -> FOL n a
  Or :: FOL n a -> FOL n a -> FOL n a
  Not :: FOL n a -> FOL n a
  Exists :: FOL n a -> FOL n a
  Extend :: FOL n a -> FOL n a
  Permute :: Permutation -> FOL n a -> FOL n a
  Mod :: FOL n a -> FOL n a

implies :: FOL n a -> FOL n a -> FOL n a
implies x y = (Not x) `And` y

forAll :: FOL n a -> FOL n a
forAll x = Not (Exists (Not x))

-- Should be instantiated with a being some sort of Set container
data Finitary a where
  Finite :: a -> Finitary a
  Cofinite :: a -> Finitary a
  deriving (Eq)

data Intersection a = Finitary a | Finitary a `Intersection` Finitary a

data Product (n :: Nat) a = Product (Vector n (Intersection a))

-- Empty list = empty set
data Union (n :: Nat) a = Union [Product n a]

type TensorTerm (n :: Nat) a = Union n a

instance (Show a) => Show (Finitary a) where
  show (Finite x) = show x
  show (Cofinite x) = show x ++ "^c"

data Algebra (n :: Nat) a where
  Base :: Finitary a -> Algebra 1 a
  Empty :: Algebra 1 a
  Univ :: Algebra 1 a
  -- Intersections only allowed in each factor of product
  (:/\) :: Algebra 1 a -> Algebra 1 a -> Algebra 1 a -- Intersection
  (:\/) :: Algebra n a -> Algebra n a -> Algebra n a -- Union
  (:><) :: Algebra 1 a -> Algebra n a -> Algebra (1 + n) a -- Cross product

infixr 5 :\/
infixr 6 :/\
infixr 7 :><

deriving instance (Show a) => Show (Algebra n a)

translate :: FOL n a -> Algebra n a
translate _ = undefined

---------------------------------------------------
-- Type classes and implementations
---------------------------------------------------

univ :: Algebra n a -> Algebra n a
univ (_ :>< y) = Univ :>< univ y
univ Empty = Univ
univ Univ = Univ
univ (Base _) = Univ
univ (_ :/\ _) = Univ
univ (x :\/ y) = univ x \/ univ y

empty :: Algebra n a -> Algebra n a
empty Empty = Empty
empty Univ = Empty
empty (Base _) = Empty
empty (_ :>< y) = Empty :>< empty y
empty (x :\/ y) = empty x :\/ empty y
empty (_ :/\ _) = Empty

class Complement a where
  compl :: a -> a

instance Complement (Finitary a) where
  compl (Finite s) = Cofinite s
  compl (Cofinite s) = Finite s

instance forall n a. Complement (Algebra n a) where
  -- Move all complements _in_ to the Finitary constructors
  compl :: Algebra n a -> Algebra n a
  compl (Base x) = Base (compl x)
  compl Empty = Univ
  compl Univ = Empty
  compl (x :/\ y) = compl x \/ compl y
  compl (x :>< y) = (Univ >< compl y) \/ (compl x >< univ y)
  compl (x :\/ y) = compl x /\ compl y

normalize :: Algebra n a -> Algebra n a
normalize (Base x) = Base x
normalize Empty = Empty
normalize Univ = Univ
-- Intersections only allowed in each factor of product
normalize (x :/\ y) = x /\ y
normalize (x :\/ y) = x \/ y
normalize (x :>< y) = x >< y

-- Move the unions up, and intersections down into 1-dim algebras
(\/) :: Algebra n a -> Algebra n a -> Algebra n a
s \/ Empty = s
Empty \/ s = s
_ \/ Univ = Univ
Univ \/ _ = Univ
x \/ y = x :\/ y

(/\) :: Algebra n a -> Algebra n a -> Algebra n a
-- Unit elements
_ /\ Empty = Empty
Empty /\ _ = Empty
s /\ Univ = s
Univ /\ s = s
-- Base elements, so n=1
Base s /\ x = Base s :/\ x
x /\ Base s = x :/\ Base s
-- Distribution into unions
-- see (28) to (30)
c /\ (d :\/ e) = (c /\ d) \/ (c /\ e)
(c :\/ d) /\ e = (c /\ e) \/ (d /\ e)
c /\ (d :/\ e) = c :/\ d :\/ e
(c :/\ d) /\ e = c :/\ d :/\ e
-- Distribution over cross product
-- dim c = dim e = 1, and dim c + dim d = dim e + dim f, so must have dim d = dim f
(c :>< d) /\ (e :>< f) = (c /\ e) >< (d /\ f)

(><) :: Algebra n a -> Algebra m a -> Algebra (n + m) a
-- Unit-cross products
Empty >< x = Empty :>< empty x
Univ >< x = Univ :>< x
Base s >< x = Base s :>< x
x >< (y :\/ z) = (x >< y) \/ (x >< z)
(x :\/ y) >< z = (x >< z) \/ (y >< z)
-- No reduction necessarry
(x :/\ y) >< z = (x :/\ y) :>< z
(x :>< y) >< z = x :>< (y >< z)

-- -- eval (C x) = fCompl $ eval x
-- Evaluations of Finitaries
evalUnion :: (Ord a) => Finitary (Set a) -> Finitary (Set a) -> Finitary (Set a)
Finite s `evalUnion` Finite t = Finite (s `union` t)
Finite s `evalUnion` Cofinite t = Cofinite (t \\ s)
Cofinite s `evalUnion` Finite t = Cofinite (s \\ t)
Cofinite s `evalUnion` Cofinite t = Cofinite (s `intersection` t)

evalIntersection :: (Ord a) => Finitary (Set a) -> Finitary (Set a) -> Finitary (Set a)
Finite s `evalIntersection` Finite t = Finite (s `intersection` t)
Finite s `evalIntersection` Cofinite t = Finite (s \\ t)
Cofinite s `evalIntersection` Finite t = Finite (t \\ s)
Cofinite s `evalIntersection` Cofinite t = Cofinite (s `union` t)

evalFinitary :: Algebra 1 (Set a) -> Finitary (Set a)
evalFinitary (Base x) = x
evalFinitary Empty = Finite (Set.empty)
evalFinitary Univ = Cofinite (Set.empty)
evalFinitary (_ :\/ _) = undefined
evalFinitary (_ :/\ _) = undefined
evalFinitary (_ :>< _) = error "Should be impossible"
