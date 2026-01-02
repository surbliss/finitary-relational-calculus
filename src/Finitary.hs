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
import Data.Set (Set)
import Data.Set qualified as Set
import GHC.TypeLits
import Prelude hiding (product)

---------------------------------------------------
-- Datatypes
---------------------------------------------------
--- Exported

--- Internal
-- We implement type-classes, which exhibit the ordering: {_}, _^c, */\*, *><*, *\/*, Empty.
-- Base: So sets, and C(sets).
-- Conventions:
-- - Union [] = Empty set
-- - Intersection [] = Universal set
-- n = Dimensions of products in the term
data Finitary a = Finite a | Cofinite a deriving (Eq, Show)
newtype Intersection a = Intersection [Finitary a] deriving (Eq, Show)
newtype Product a = Product (NonEmpty (Intersection a)) deriving (Eq, Show)
newtype Union a = Union [Product a] deriving (Eq, Show)

-- Wrapper with dimension-info, i.e. length of Products
newtype Term (n :: Nat) a = Term (Union a) deriving (Eq, Show)

---------------------------------------------------
-- Exported smart constructors
---------------------------------------------------
-- TODO
complement :: Term n a -> Term n a
complement (Term x) = Term $ compl' x

(/\) :: Term n a -> Term n a -> Term n a
Term x /\ Term y = Term (x */\* y)

(><) :: Term n a -> Term m a -> Term (n + m) a
Term x >< Term y = Term (x *><* y)

(\/) :: Term n a -> Term n a -> Term n a
Term x \/ Term y = Term (x *\/* y)

-- TODO: Permutation, projection and diagonalization

finite :: a -> Term 1 a
finite x = Term $ single $ Finite x

cofinite :: a -> Term 1 a
cofinite x = Term $ single $ Cofinite x

empty :: Term n a
empty = Term emptyUnion

univ :: Term 1 a
univ = Term univUnion

---------------------------------------------------
-- Internals constructors
---------------------------------------------------
--- Helpers
-- Checks that products are not emptyUnio, internal invariant to be maintained
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

  Intersection [] *\/* _ = univUnion
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
  Union [] *><* _ = emptyUnion
  _ *><* Union [] = emptyUnion
  Union (x : xs) *><* Union (y : ys) =
    (x *><* y)
      *\/* (Union [x] *><* Union ys)
      *\/* (Union xs *><* Union [y])
      *\/* (Union xs *><* Union ys)

  -- Ugly, but this is canonical representation of "Univ"
  Union [Product (Intersection [] :| [])] *\/* _ = univUnion
  _ *\/* Union [Product (Intersection [] :| [])] = univUnion
  x *\/* Union [] = x
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
