{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Finitary (
  Term,
  Finitary,
  Intersection,
  Product,
  Union,
  empty,
  univ,
  finite,
  cofinite,
  complement,
  (/\),
  (\/),
  (><),
  pprint,
) where

import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty ((:|)), nonEmpty, toList)
import GHC.TypeLits
import Prelude hiding (product)

---------------------------------------------------
-- Datatypes
---------------------------------------------------

{- | We implement type-classes, which exhibit the ordering: {_}, _^c, */\*, *><*, *\/*, Empty.
Base: Sets, and C(sets).

Conventions:
- Union [] = Empty set
- Intersection [] = Universal set
- n = Dimensions of products in the term
-}
data Finitary a = Finite a | Cofinite a deriving (Eq, Show)

newtype Intersection a = Intersection [Finitary a] deriving (Eq, Show)
newtype Product a = Product (NonEmpty (Intersection a)) deriving (Eq, Show)
newtype Union a = Union [Product a] deriving (Eq, Show)

-- Wrapper with dimension-info, i.e. length of Products
newtype Term (n :: Nat) a = Term (Union a) deriving (Eq, Show)

---------------------------------------------------
-- Exported constructors
---------------------------------------------------
finite :: a -> Term 1 a
finite x = Term $ single $ Finite x

cofinite :: a -> Term 1 a
cofinite x = Term $ single $ Cofinite x

-- Need to specify dimension manually
empty :: Term n a
empty = Term Empty

-- Always dim 1, for higher dim do univ >< univ >< ...
univ :: Term 1 a
univ = Term Univ1

complement :: Term n a -> Term n a
complement (Term x) = Term $ compl' x

(/\) :: Term n a -> Term n a -> Term n a
Term x /\ Term y = Term (x */\* y)

(><) :: Term n a -> Term m a -> Term (n + m) a
Term x >< Term y = Term (x *><* y)

(\/) :: Term n a -> Term n a -> Term n a
Term x \/ Term y = Term (x *\/* y)

-- TODO: Permutation, projection and diagonalization
perm :: [Int] -> Term n a -> Term n a
perm = undefined

-- If result is type Term 0 a, then it should always be the empty set
-- Also remember to rerun \/, so terms can be normalized
proj :: Term (n + 1) a -> Term n a
proj = undefined

diag :: Term (n) a -> Term (n + 1) a
diag = undefined

---------------------------------------------------
-- Internals constructors
---------------------------------------------------
--- Helpers
-- Checks that products are not emptyUnio, internal invariant to be maintained
pattern Empty :: Union a
pattern Empty = Union []

-- One-dimension Univeral
pattern Univ1 :: Union a
pattern Univ1 = Union [Product (Intersection [] :| [])]
emptyUnion :: Union a
emptyUnion = Union []

univUnion :: Union a
univUnion = intersection $ []

-- Wraps type in a Union (so, as a term)
single :: Finitary a -> Union a
single x = intersection [x]

intersection :: [Finitary a] -> Union a
intersection xs = product $ Intersection xs :| []

product :: NonEmpty (Intersection a) -> Union a
product xs = Union [Product xs]

--- Internal computations
-- NOT to be exported, helper-functions for internal algebra-calculations
class InternalAlgebra t where
  -- Each type is responsible for one of these, the rest propagates:
  compl' :: t a -> Union a -- Finitary
  (*/\*) :: t a -> t a -> Union a -- Intersection
  (*><*) :: t a -> t a -> Union a -- Product
  (*\/*) :: t a -> t a -> Union a -- Union

instance InternalAlgebra Finitary where
  compl' (Finite x) = single $ Cofinite x
  compl' (Cofinite x) = single $ Finite x

  x */\* y = single x */\* single y
  x *><* y = single x *><* single y
  x *\/* y = single x *\/* single y

instance InternalAlgebra Intersection where
  -- Intersection should handle Univ-rules
  compl' (Intersection []) = emptyUnion
  -- (21), i.e. DeMorgan
  compl' (Intersection (x : xs)) = compl' x *\/* compl' (Intersection xs)

  -- Note that xs/ys = [] acts asunivUnion here!
  Intersection xs */\* Intersection ys = intersection $ xs <> ys
  Intersection xs *><* Intersection ys = intersection xs *><* intersection ys

  Intersection [] *\/* _ = Univ1
  _ *\/* Intersection [] = univUnion
  Intersection xs *\/* Intersection ys = intersection xs *\/* intersection ys

instance InternalAlgebra Product where
  -- (22)
  compl' (Product (x :| xs)) = case xs of
    [] -> compl' x
    y : ys ->
      (compl' x *><* univs (length ys))
        *\/* (univUnion *><* compl' (product (y :| ys)))
      where
        u = Intersection []
        univs n = product $ u :| replicate (n - 1) u

  -- (30)
  Product (x :| xs) */\* Product (y :| ys) =
    case (nonEmpty xs, nonEmpty ys) of
      (Nothing, Nothing) -> x */\* y
      (Just xs', Just ys') -> (x */\* y) *><* (product xs' */\* product ys')
      (Nothing, Just _) -> error "Right product longer than left should not be possible"
      (Just _, Nothing) -> error "Left product longer than right should not be possible"

  Product xs *><* Product ys = product (xs <> ys)

  Product xs *\/* Product ys = product xs *\/* product ys

instance InternalAlgebra Union where
  -- DeMorgan
  compl' (Union []) = emptyUnion
  compl' (Union [x]) = compl' x
  compl' (Union (x : xs)) = compl' x */\* compl' (Union xs)

  Union [] */\* _ = emptyUnion
  _ */\* Union [] = emptyUnion
  -- (28)-(29)
  Union (x : xs) */\* Union (y : ys) =
    (x */\* y)
      *\/* (Union [x] */\* Union ys)
      *\/* (Union xs */\* Union [y])

  -- (31)-(32) + emptyUnion products
  Union [] *><* _ = Empty
  _ *><* Union [] = Empty
  Union (x : xs) *><* Union (y : ys) =
    (x *><* y)
      *\/* (Union [x] *><* Union ys)
      *\/* (Union xs *><* Union [y])
      *\/* (Union xs *><* Union ys)

  -- Ugly, but this is canonical representation of "Univ"
  -- NOTE: Maybe this could be more efficent, than looping every time
  Union xs *\/* Union ys
    | isUniv xs = Union xs
    | isUniv ys = Union ys
    where
      isUniv = all isUnivProduct
      isUnivProduct (Product (z :| zs)) =
        isEmptyIntersection z && all isEmptyIntersection zs
      isEmptyIntersection (Intersection []) = True
      isEmptyIntersection (Intersection (_ : _)) = False
  x *\/* Empty = x
  Empty *\/* x = x
  -- Note that xs/ys = [] acts as empty-set
  Union xs *\/* Union ys = Union (xs <> ys)

---------------------------------------------------
-- Pretty-printing
---------------------------------------------------
class PrettyShow a where
  pshow :: a -> String

withOp :: (PrettyShow a) => String -> [a] -> String
withOp op xs = intercalate op (map pshow xs)

withParens :: String -> String
withParens s = "(" ++ s ++ ")"

instance PrettyShow String where
  pshow xs = xs

instance PrettyShow Int where
  pshow xs = show xs

instance (PrettyShow a) => PrettyShow (Finitary a) where
  pshow (Finite x) = pshow x
  pshow (Cofinite x) = pshow x ++ "ᶜ"

instance (PrettyShow a) => PrettyShow (Intersection a) where
  pshow (Intersection []) = "𝕌"
  pshow (Intersection [x]) = pshow x
  pshow (Intersection xs) = withOp "∩" xs

instance (PrettyShow a) => PrettyShow (Product a) where
  pshow (Product (x :| [])) = pshow x
  pshow (Product xs) = withParens $ withOp " × " (toList xs)

instance (PrettyShow a) => PrettyShow (Union a) where
  pshow (Union []) = "∅"
  pshow (Union [x]) = pshow x
  pshow (Union xs) = withOp " ∪ " xs

instance (PrettyShow a) => PrettyShow (Term n a) where
  pshow (Term x) = pshow x

pprint :: (PrettyShow a) => a -> IO ()
pprint = putStrLn . pshow
