{-# LANGUAGE GHC2024 #-}

module Set.Algebra
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
import PrettyShow

-- data Base a = With (Set a) | Without (Set a) deriving (Eq, Show)

-- newtype Product a = Product (NonEmpty (Base a)) deriving (Eq, Show)

data Base a = With (Set a) | Without (Set a) deriving (Eq, Show, Ord)

data Algebra a where
  Base :: Base a -> Algebra a
  Product :: NonEmpty (Algebra a) -> Algebra a
  Union :: NonEmpty (Algebra a) -> Algebra a
  deriving (Eq, Show)

---------------------------------------------------
-- ASSERTIONS: These are for assertions that data structure is represented correctly.
---------------------------------------------------
-- Can be removed, once this is tested thoroughly
-- This asserts that the current form is a normal form. That is, Base < Complement < Product < Union
-- At some point, it might make sense to move 'Complement' up

--- Only use on products
dimProduct :: Algebra a -> Int
dimProduct (Product xs) = NE.length xs
dimProduct _ = error "Took dim on non-product"

dim :: Algebra a -> Int
dim (Base _) = 1
dim xs@(Product _) = dimProduct xs
dim (Union xs) = firstDim
  where
    dims = dimProduct <$> xs
    firstDim = NE.head dims
    !_ = assert $ and $ (firstDim ==) <$> NE.tail dims

isBase :: Algebra a -> Bool
isBase (Base _) = True
isBase _ = False

isValidProduct :: Algebra a -> Bool
isValidProduct (Product xs) = all isBase xs
isValidProduct _ = False

isValidUnion :: Algebra a -> Bool
isValidUnion (Union xs) = all isValidProduct xs && constDim
  where
    -- Dimensions (crash if not products!)
    dims = dimProduct <$> xs
    constDim = and $ (== NE.head dims) <$> NE.tail dims
isValidUnion _ = False

isValid :: Algebra a -> Bool
isValid x = isBase x || isValidProduct x || isValidUnion x

---------------------------------------------------
-- Assertion stuff done
---------------------------------------------------

fins :: (Ord a) => [a] -> Algebra a
fins xs = Base $ With $ Set.fromList xs

empty1 :: Algebra a
empty1 = Base $ With $ Set.empty

empty :: Int -> Algebra a
empty n | n < 1 = error "Non-positive univ"
empty 1 = empty1
empty n = Product (NE.fromList (replicate n empty1))

-- 1-dimensional U
univ1 :: Algebra a
univ1 = Base $ Without $ Set.empty

univ :: Int -> Algebra a
univ n | n < 1 = error "Non-positive univ"
univ 1 = univ1
univ n = Product (NE.fromList (replicate n univ1))

isEmpty :: Algebra a -> Bool
isEmpty s = assert (isValid s) $ case s of
  Base x -> isEmptyBase x
  Product xs -> any isEmpty xs
  Union xs -> all isEmpty xs
  where
    isEmptyBase (With x) = Set.null x
    isEmptyBase (Without _) = False

toEmpty :: Algebra a -> Algebra a
toEmpty s = assert (isValid s) $ case s of
  Base _ -> empty1
  Product (_ :| []) -> empty1
  Product xs@(_ :| _ : _) -> empty $ length xs
  Union (x :| _) -> toEmpty x

isUniv :: Algebra a -> Bool
isUniv s = assert (isValid s) $ case s of
  Base x -> isUnivBase x
  Product xs -> all isUniv xs
  Union xs -> any isUniv xs
  where
    isUnivBase (With _) = False
    isUnivBase (Without x) = Set.null x

toUniv :: Algebra a -> Algebra a
toUniv s = assert (isValid s) $ case s of
  Base _ -> univ1
  Product (_ :| []) -> univ1
  Product xs@(_ :| _ : _) -> univ (length xs)
  Union (x :| _) -> toUniv x

single :: Algebra a -> Algebra a
single s = assert (isValid s) $ case s of
  x@(Base _) -> Union $ (Product (x :| [])) :| []
  x@(Product _) -> Union $ x :| []
  Union _ -> error "Why take single on a union"

--- All the below should return unions! So the types are consistent
--- Actually, nvm, lets try without! Just simplify as much as possible
compl :: (Ord a) => Algebra a -> Algebra a
compl s = assert (isValid s) $ case s of
  Base (With x) -> Base $ Without x
  Base (Without x) -> Base $ With x
  Product (x :| []) -> compl x
  Product (x :| x' : xs) -> (compl x >< univ (dim rest)) \/ (univ1 >< compl rest)
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

(/\) :: (Ord a) => Algebra a -> Algebra a -> Algebra a
s /\ s' = assert (isValid s || isValid s' || dim s == dim s') $ case (s, s') of
  (_, _) | isEmpty s -> empty $ dim s
  (_, _) | isEmpty s' -> empty $ dim s'
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

(\/) :: (Ord a) => Algebra a -> Algebra a -> Algebra a
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

(><) :: (Ord a) => Algebra a -> Algebra a -> Algebra a
s >< s' = assert (isValid s || isValid s') $ case (s, s') of
  --- Simplify if argument empty (Nothing happens if univ)
  (_, _) | isEmpty s || isEmpty s' -> empty $ dim s + dim s'
  --- Base operations (figure 2)
  (x@(Base _), y@(Base _)) -> Product (x :| [y])
  --- Singleton simplifications
  (Union (x :| []), y) -> x >< y
  (Product (x :| []), y) -> x >< y
  (x, Union (y :| [])) -> x >< y
  (x, Product (y :| [])) -> x >< y
  --- Non-trivial Unions
  -- (32)
  -- (Union (x :| x' : xs), y) -> (x >< y) \/ (Union (x' :| xs) >< y)
  (Union xs@(_ :| _ : _), y) -> Union $ (>< y) <$> xs
  -- (31)
  -- (x, Union (y :| y' : ys)) -> (x >< y) \/ (x >< Union (y' :| ys))
  (x, Union ys@(_ :| _ : _)) -> Union $ (x ><) <$> ys
  -- (x@(Base _), Union (y :| y' : ys)) -> (x >< y) \/ (x >< Union (y' :| ys))
  -- (32)
  --- Products (Now there are no unions!)
  (Product xs@(_ :| _ : _), Product ys@(_ :| _ : _)) -> Product $ xs <> ys
  (x@(Base _), Product xs@(_ :| _ : _)) -> Product $ x <| xs
  (Product xs@(_ :| _ : _), x@(Base _)) -> Product $ NE.appendList xs [x]

---------------------------------------------------
-- FOL Query functions
---------------------------------------------------
--- Note that we only allow projections on dim > 2.
proj :: (Ord a) => Int -> Algebra a -> Algebra a
proj i _ | i < 1 = error "non-positive projection"
proj i s | i > dim s = error "proj on i > dim"
proj i s = assert (isValid s || dim s > 1) $ case s of
  Base _ -> error "base, dim = 1 of proj"
  Product (_ :| []) -> error "prod, dim = 1 of proj"
  Product (_ :| (x : xs)) -> case i of
    1 -> Product $ x :| xs
    _ -> proj (i - 1) $ Product (x :| xs)
  Union (x :| []) -> proj i x
  Union xs@(_ :| _ : _) -> foldl (\/) (empty (dim s)) (proj i <$> xs)

-- proj i (Union xs) = foldl (\/) empty (map (projProd i) xs)
---------------------------------------------------
-- PrettyShow implementation
---------------------------------------------------
instance (PrettyShow a) => PrettyShow (Base a) where
  pshow (With x) | Set.null x = "∅"
  pshow (With x) = pshow x
  pshow (Without x) | Set.null x = "𝕌"
  pshow (Without x) = pshow x ++ "ᶜ"

instance (PrettyShow a) => PrettyShow (Algebra a) where
  pshow (Base x) = pshow x
  pshow (Product xs) = withParens $ intercalate " × " (map pshow $ NE.toList xs)
  pshow (Union xs) = withParens $ intercalate " ∪ " (map pshow $ NE.toList xs)
