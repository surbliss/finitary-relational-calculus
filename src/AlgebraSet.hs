{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternSynonyms #-}

{- | Internal constructors that maintain ordering of algebra terms.
Not to be exported directly, but to be used internally only
-}
module AlgebraSet
where

-- (
--   Base (..)
--   , Product (..)
-- Finitary (..),
-- Intersection (..),
-- Product (..),
-- Union (..),
-- InternalAlgebra (..),
-- PrettyShow (..),
-- pprint,
-- empty,
-- univ1,
-- perm,
-- proj,
-- diag,
-- )

-- import Data.List (intercalate)
import Control.Exception (assert)
import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty ((:|)), (<|))
import Data.List.NonEmpty qualified as NE
import Data.Set (Set)
import Data.Set qualified as Set

-- data Base a = With (Set a) | Without (Set a) deriving (Eq, Show)

-- newtype Product a = Product (NonEmpty (Base a)) deriving (Eq, Show)

data Base a = With (Set a) | Without (Set a) deriving (Eq, Show, Ord)

data SetAlgebra a where
  Base :: Base a -> SetAlgebra a
  Product :: NonEmpty (SetAlgebra a) -> SetAlgebra a
  Union :: NonEmpty (SetAlgebra a) -> SetAlgebra a
  deriving (Eq, Show)

---------------------------------------------------
-- ASSERTIONS: These are for assertions that data structure is represented correctly.
---------------------------------------------------
-- Can be removed, once this is tested thoroughly
-- This asserts that the current form is a normal form. That is, Base < Complement < Product < Union
-- At some point, it might make sense to move 'Complement' up

--- Only use on products
dimProduct :: SetAlgebra a -> Int
dimProduct (Product xs) = NE.length xs
dimProduct _ = error "Took dim on non-product"

dim :: SetAlgebra a -> Int
dim (Base _) = 1
dim xs@(Product _) = dimProduct xs
dim (Union xs) = firstDim
  where
    dims = dimProduct <$> xs
    firstDim = NE.head dims
    !_ = assert $ and $ (firstDim ==) <$> NE.tail dims

isBase :: SetAlgebra a -> Bool
isBase (Base _) = True
isBase _ = False

isValidProduct :: SetAlgebra a -> Bool
isValidProduct (Product xs) = all isBase xs
isValidProduct _ = False

isValidUnion :: SetAlgebra a -> Bool
isValidUnion (Union xs) = all isValidProduct xs && constDim
  where
    -- Dimensions (crash if not products!)
    dims = dimProduct <$> xs
    constDim = and $ (== NE.head dims) <$> NE.tail dims
isValidUnion _ = False

isValid :: SetAlgebra a -> Bool
isValid x = isBase x || isValidProduct x || isValidUnion x

---------------------------------------------------
-- Assertion stuff done
---------------------------------------------------

fins :: (Ord a) => [a] -> SetAlgebra a
fins xs = Base $ With $ Set.fromList xs

empty1 :: SetAlgebra a
empty1 = Base $ With $ Set.empty

-- 1-dimensional U
univ1 :: SetAlgebra a
univ1 = Base $ Without $ Set.empty

isEmpty :: SetAlgebra a -> Bool
isEmpty s = assert (isValid s) $ case s of
  Base x -> isEmptyBase x
  Product xs -> any isEmpty xs
  Union xs -> all isEmpty xs
  where
    isEmptyBase (With x) = Set.null x
    isEmptyBase (Without _) = False

toEmpty :: SetAlgebra a -> SetAlgebra a
toEmpty s = assert (isValid s) $ case s of
  Base _ -> empty1
  Product xs -> Product (const empty1 <$> xs)
  Union (x :| _) -> toEmpty x

isUniv :: SetAlgebra a -> Bool
isUniv s = assert (isValid s) $ case s of
  Base x -> isUnivBase x
  Product xs -> all isUniv xs
  Union xs -> any isUniv xs
  where
    isUnivBase (With _) = False
    isUnivBase (Without x) = Set.null x

toUniv :: SetAlgebra a -> SetAlgebra a
toUniv s = assert (isValid s) $ case s of
  Base _ -> univ1
  Product xs -> Product (const univ1 <$> xs)
  Union xs -> Union (const univ1 <$> xs)

single :: SetAlgebra a -> SetAlgebra a
single s = assert (isValid s) $ case s of
  x@(Base _) -> Union $ (Product (x :| [])) :| []
  x@(Product _) -> Union $ x :| []
  Union _ -> error "Why take single on a union"

--- All the below should return unions! So the types are consistent
--- Actually, nvm, lets try without! Just simplify as much as possible
compl :: (Ord a) => SetAlgebra a -> SetAlgebra a
compl s = assert (isValid s) $ case s of
  Base (With x) -> Base $ Without x
  Base (Without x) -> Base $ With x
  Product (x :| []) -> compl x
  Product (x :| x' : xs) -> (compl x >< toUniv rest) \/ (univ1 >< compl rest)
    where
      rest = Product (x' :| xs)
  Union (x :| []) -> compl x
  Union (x :| x' : xs) -> compl x /\ compl rest
    where
      rest = Union (x' :| xs)

baseIntersection :: (Ord a) => Base a -> Base a -> Base a
baseIntersection s s' = case (s, s') of
  (With x, With y) -> With $ Set.intersection x y
  (With x, Without y) -> With $ x Set.\\ y
  (Without x, With y) -> With $ y Set.\\ x
  (Without x, Without y) -> Without $ Set.union x y

(/\) :: (Ord a) => SetAlgebra a -> SetAlgebra a -> SetAlgebra a
s /\ s' = assert (isValid s || isValid s' || dim s == dim s') $ case (s, s') of
  (_, _) | isEmpty s -> toEmpty s
  (_, _) | isEmpty s' -> toEmpty s'
  (_, _) | isUniv s -> s'
  (_, _) | isUniv s' -> s
  (Base x, Base y) -> Base $ baseIntersection x y
  (Union (x :| []), y) -> x /\ y
  (Product (x :| []), y) -> x /\ y
  (x, Union (y :| [])) -> x /\ y
  (x, Product (y :| [])) -> x /\ y
  --- Non-trivial Unions
  -- (28)
  (x, Union (y :| y' : ys)) -> (x /\ y) \/ (x /\ Union (y' :| ys))
  -- (29)
  (Union (x :| x' : xs), y) -> (x /\ y) \/ (Union (x' :| xs) /\ y)
  -- (32)
  --- Products (Now there are no unions!). Also, the assert makes sure the dimensions are equal, so just error in those cases (Basically, something non-product with something product)
  (Product (x :| x' : xs), Product (y :| y' : ys)) ->
    (x /\ y) >< (Product (x' :| xs) /\ Product (y' :| ys))
  (Base _, Product (_ :| _ : _)) -> error "Base inter dim>2"
  (Product (_ :| _ : _), Base _) -> error "dim>2 inter base"

baseUnion :: (Ord a) => Base a -> Base a -> Base a
baseUnion s s' = case (s, s') of
  (With x, With y) -> With $ Set.union x y
  (With x, Without y) -> Without $ y Set.\\ x
  (Without x, With y) -> Without $ x Set.\\ y
  (Without x, Without y) -> Without $ Set.intersection x y

(\/) :: (Ord a) => SetAlgebra a -> SetAlgebra a -> SetAlgebra a
s \/ s' = assert (isValid s || isValid s || dim s == dim s') $ case (s, s') of
  (_, _) | isEmpty s -> s'
  (_, _) | isEmpty s' -> s
  (_, _) | isUniv s -> toUniv s
  (_, _) | isUniv s' -> toUniv s
  (Base x, Base y) -> Base $ baseUnion x y
  -- Simplify singletons
  (Union (x :| []), y) -> x \/ y
  (Product (x :| []), y) -> x \/ y
  (x, Union (y :| [])) -> x \/ y
  (x, Product (y :| [])) -> x \/ y
  -- Propagate Bases (should never end in a Union)
  (x@(Base _), Union (y :| y' : ys)) -> x \/ y \/ (Union (y' :| ys))
  --- Reordering here, but shouldn't really matter as it ends up as 'base'
  (Union (x :| x' : xs), y@(Base _)) -> x \/ y \/ (Union (x' :| xs))
  --- Non-trivial Unions. Really, this should _only_ happen if we have products inside the union, so we have to just do a formal union here!
  -- Only way to simplify, is if some terms are strictly contained in others, but that is too expensive to check
  (Union xs@(_ :| _ : _), Union ys@(_ :| _ : _)) -> Union $ xs <> ys
  -- Actually, just reorder here, as prepending is faster than appending
  (xs@(Product (_ :| _ : _)), Union ys@(_ :| _ : _)) -> Union $ xs <| ys
  (Union xs@(_ :| _ : _), ys@(Product (_ :| _ : _))) -> Union $ ys <| xs
  --- Products (Now there are no unions!)
  (xs@(Product (_ :| _ : _)), ys@(Product (_ :| _ : _))) -> Union (xs :| [ys])
  ((Base _), Product (_ :| _ : _)) -> error "Base union dim>2"
  (Product (_ :| _ : _), (Base _)) -> error "dim>2 union Base"

(><) :: (Ord a) => SetAlgebra a -> SetAlgebra a -> SetAlgebra a
s >< s' = assert (isValid s || isValid s') $ case (s, s') of
  --- Simplify if argument empty (Nothing happens if univ)
  (_, _) | isEmpty s || isEmpty s' -> toEmpty s >< toEmpty s'
  --- Base operations (figure 2)
  (x@(Base _), y@(Base _)) -> Product (x :| [y])
  --- Singleton simplifications
  (Union (x :| []), y) -> x >< y
  (Product (x :| []), y) -> x >< y
  (x, Union (y :| [])) -> x >< y
  (x, Product (y :| [])) -> x >< y
  --- Non-trivial Unions
  -- (32)
  (Union (x :| x' : xs), y) -> (x >< y) \/ (Union (x' :| xs) >< y)
  -- (31)
  (x, Union (y :| y' : ys)) -> (x >< y) \/ (x >< Union (y' :| ys))
  -- (x@(Base _), Union (y :| y' : ys)) -> (x >< y) \/ (x >< Union (y' :| ys))
  -- (32)
  --- Products (Now there are no unions!)
  (Product xs@(_ :| _ : _), Product ys@(_ :| _ : _)) -> Product $ xs <> ys
  (x@(Base _), Product xs@(_ :| _ : _)) -> Product $ x <| xs
  (Product xs@(_ :| _ : _), x@(Base _)) -> Product $ NE.appendList xs [x]

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

instance (PrettyShow a) => PrettyShow (Set a) where
  pshow xs = "{" ++ intercalate ", " (map pshow (Set.elems xs)) ++ "}"

instance (PrettyShow a) => PrettyShow (Base a) where
  pshow (With x) | Set.null x = "∅"
  pshow (With x) = pshow x
  pshow (Without x) | Set.null x = "𝕌"
  pshow (Without x) = pshow x ++ "ᶜ"

instance (PrettyShow a) => PrettyShow (SetAlgebra a) where
  pshow (Base x) = pshow x
  pshow (Product xs) = withParens $ intercalate " × " (map pshow $ NE.toList xs)
  pshow (Union xs) = withParens $ intercalate " ∪ " (map pshow $ NE.toList xs)

-- instance (PrettyShow a) => PrettyShow (Intersection a) where
--   pshow (Intersection []) = "𝕌"
--   pshow (Intersection [x]) = pshow x
--   pshow (Intersection xs) = withOp "∩" xs

-- instance (PrettyShow a) => PrettyShow (Product a) where
--   pshow (Product (x :| [])) = pshow x
--   pshow (Product xs) = withParens $ withOp " × " (toList xs)

-- instance (PrettyShow a) => PrettyShow (Union a) where
--   pshow (Union []) = "∅"
--   pshow (Union [x]) = pshow x
--   pshow (Union xs) = withOp " ∪ " xs

pprint :: (PrettyShow a) => a -> IO ()
pprint = putStrLn . pshow
