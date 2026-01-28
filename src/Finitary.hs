{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Finitary where

import Data.Function ((&))
import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty ((:|)), nonEmpty, toList)
import Data.Set (Set)
import Data.Set qualified as Set
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
data Finitary a = Finite a | Cofinite a deriving (Eq, Show, Functor)

newtype Intersection a = Intersection [Finitary a] deriving (Eq, Show, Functor)

newtype Product a = Product (NonEmpty (Intersection a)) deriving (Eq, Show, Functor)
newtype Union a = Union [Product a] deriving (Eq, Show, Functor)

-- Wrapper with dimension-info, i.e. length of Products
newtype Term (n :: Nat) a = Term (Union a) deriving (Eq, Show, Functor)

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

diag :: Term n a -> Term (n + 1) a
diag = undefined

-- join?

-- Evaluation: None if 'cofinite' returned
eval :: Term n (Set a) -> Maybe (Set [a])
eval (Term _) = undefined

---------------------------------------------------
-- Internals constructors
---------------------------------------------------
--- Evaluation:

-- Each element is a tuple (shound be homogenous)
-- newtype Element a = Element [a] deriving (Show, Eq, Ord)
-- newtype Result a = Result (Finitary (Set (Element a))) deriving (Show, Eq)
data Result s a = With (s [a]) | Without (s [a]) deriving (Functor)

complRes :: Result s a -> Result s a
complRes (With x) = Without x
complRes (Without x) = With x

interRes :: (Ord a) => Result Set a -> Result Set a -> Result Set a
With x `interRes` With y = With $ Set.intersection x y
With x `interRes` Without y = With $ x Set.\\ y
Without x `interRes` With y = With $ y Set.\\ x
Without x `interRes` Without y = Without $ Set.union x y

-- (13)-(15)
unionRes :: (Ord a) => Result Set a -> Result Set a -> Result Set a
With x `unionRes` With y = With $ Set.union x y
With x `unionRes` Without y = Without $ y Set.\\ x
Without x `unionRes` With y = Without $ x Set.\\ y
Without x `unionRes` Without y = Without $ Set.intersection x y

cartProd :: (Ord a) => Set [a] -> Set [a] -> Set [a]
xs `cartProd` ys = Set.cartesianProduct xs ys & Set.map (\(x, y) -> x <> y)

-- where
-- (xs, ys) = Set.cartesianProduct s u

-- NOTE: When applying this, remember to check for any empty sets!
prodRes :: (Ord a) => Result Set a -> Result Set a -> Maybe (Result Set a)
With xs `prodRes` With ys = Just $ With $ cartProd xs ys
_ `prodRes` _ = Nothing

-- eval' :: Finitary (Set a) -> With (Set [a])
-- class Eval s t where
--   eval' :: (Ord a) => t (s a) -> Result s a

-- instance Eval Set Finitary where
--   eval' (Finite s) = With $ Set.map List.singleton s
--   eval' (Cofinite s) = Without $ Set.map List.singleton s

-- instance Eval Set Intersection where
--   eval' (Intersection is) = With $ _
--     where
--       sets = eval' <$> is

-- instance Eval (Finitary (Set a)) where
--   eval' (Finite x) = With $ Set.map List.singleton x

--- With a /\ With a = ...
-- singleElement :: a -> Element a
-- singleElement x = Element [x]

-- elements :: Finitary (Set a) -> Result a
-- elements (Finite s) = Result (Finite (Set.map singleElement s))
-- elements (Cofinite s) = Result (Finite (Set.map singleElement s))

--- Result helpers
-- interResult :: Result a -> Result a -> Result a
-- Result x `interResult` Result y = _
--    where
--      Finite x inter Finite y

--- All inner elements are lists of length 1
-- evalIntersection :: (Ord a) => Intersection (Set a) -> Result (Set [a])
-- evalIntersection (Intersection xs) = Set.map List.singleton <$> inter
--   where
--     -- (16)-(18)
--     With s `interFin` Finite u = With $ Set.intersection s u
--     With s `interFin` Cofinite u = With $ s Set.\\ u
--     Without s `interFin` Finite u = With $ u Set.\\ s
--     Without s `interFin` Cofinite u = Without $ Set.union s u
--     inter = foldl interFin (Without Set.empty) xs

-- singletons (Finite x) = Finite $ Set.map List.singleton x
-- singletons (Cofinite x) = Cofinite $ Set.map List.singleton x

-- For evaluating a product, to get a well-definde finitary, all the terms have
-- to be Finite, or all the terms have to be Cofinite
-- evalProduct :: (Ord a) => Product (Set a) -> Maybe (Result (Set [a]))
-- evalProduct (Product (p :| ps)) = foldM prodFolder i is
--   where
--     i = evalIntersection p
--     is = map evalIntersection ps
--     -- Folding function
--     prodFolder :: Result (Set [a]) -> Finitary (Set a) -> Maybe (Result (Set [a]))
--     prodFolder xs y = case (xs, y) of
--       (With xs', Finite y') -> Just $ Finite $ xs' <> [y']
--       (Cofinite xs', Cofinite y') -> Just $ Cofinite $ xs' <> [y']
--       _ -> Nothing

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

  -- Note that xs/ys = [] acts as empty-set, so these lines are technically unecessary
  x *\/* Empty = x
  Empty *\/* x = x
  -- Filter univs away here!
  Union xs *\/* Union ys = Union (filter (not . isUniv) $ xs <> ys)
    where
      isUniv (Product (z :| zs)) =
        isEmptyIntersection z && all isEmptyIntersection zs
      isEmptyIntersection (Intersection []) = True
      isEmptyIntersection (Intersection (_ : _)) = False

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
