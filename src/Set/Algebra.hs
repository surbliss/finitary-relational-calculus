{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE OverloadedLists #-}

module Set.Algebra
where

import Control.Exception (assert)
import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty ((:|)), (<|))
import Data.List.NonEmpty qualified as NE
import Data.IntSet qualified as IntSet
import PrettyShow
import Data.Set (Set)
import Data.Set qualified as Set

type IntSet = IntSet.IntSet

data Base = With IntSet | Without IntSet deriving (Eq, Show, Ord)

data Algebra where
  Base :: Base -> Algebra
  --- Always dim >= 2
  Product :: NonEmpty Algebra -> Algebra
  Union :: Set Algebra  -> Algebra
  deriving (Eq, Show, Ord)

--- Non-normalized version
data Query where
  QBase :: Base -> Query
  (:><) :: Query -> Query -> Query
  (:\/) :: Query -> Query -> Query

debugShow ::  Algebra -> String
debugShow x@(Base _) | isEmpty x = "Ø"
debugShow x@(Base _) | isUniv x = "𝕌"
debugShow (Base (With _)) = "F"
debugShow (Base (Without _)) = "C"
debugShow (Product xs) = "(P:" ++ show (debugShow <$> xs) ++ ")"
debugShow (Union xs) = "(U:" ++ show (debugShow `Set.map` xs) ++ ")"

---------------------------------------------------
-- ASSERTIONS: These are for assertions that data structure is represented correctly.
---------------------------------------------------
-- Can be removed, once this is tested thoroughly
-- This asserts that the current form is a normal form. That is, Base < Complement < Product < Union
-- At some point, it might make sense to move 'Complement' up

dim :: Algebra -> Int
dim (Base _) = 1
dim (Product xs) = length xs
dim (Union xs) = assert allSameDim $ firstDim
  where
    dims = Set.map dim xs
    allSameDim = all (== firstDim) dims
    firstDim = Set.elemAt 0 dims

isBase :: Algebra -> Bool
isBase (Base _) = True
isBase _ = False

isValidProduct :: Algebra -> Bool
isValidProduct (Product xs) = all isBase xs
isValidProduct _ = False

isValidUnion :: Algebra -> Bool
isValidUnion s@(Union xs) =
  (dim s == 1 && all isBase xs) || (dim s > 1 && all isValidProduct xs)
isValidUnion _ = False

isValid :: Algebra -> Bool
isValid x = isBase x || isValidProduct x || isValidUnion x

---------------------------------------------------
-- Assertion stuff done
---------------------------------------------------

fins :: [Int] -> Algebra
fins xs = Base $ With $ IntSet.fromList xs

empty :: Int -> Algebra
empty n | n < 1 = error "Non-positive univ"
empty 1 = Base $ With $ IntSet.empty
empty n = Product (NE.fromList (replicate n (empty 1)))

univ :: Int -> Algebra
univ n | n < 1 = error "Non-positive univ"
univ 1 = Base $ Without $ IntSet.empty
univ n = Product (NE.fromList (replicate n (univ 1)))

isEmpty :: Algebra -> Bool
isEmpty s = assert (isValid s) $ case s of
  Base x -> isEmptyBase x
  Product xs -> any isEmpty xs
  Union xs -> all isEmpty xs
  where
    isEmptyBase (With x) = IntSet.null x
    isEmptyBase (Without _) = False

isUniv :: Algebra -> Bool
isUniv s = assert (isValid s) $ case s of
  Base x -> isUnivBase x
  Product xs -> all isUniv xs
  Union xs -> any isUniv xs
  where
    isUnivBase (With _) = False
    isUnivBase (Without x) = IntSet.null x

--- All the below should return unions! So the types are consistent
--- Actually, nvm, lets try without! Just simplify as much as possible
compl :: Algebra -> Algebra
compl s = case s of
  Base (With x) -> Base $ Without x
  Base (Without x) -> Base $ With x
  Product (x :| []) -> compl x
  Product (x :| x' : xs) -> (compl x >< univ (1 + length xs)) \/ (univ 1 >< compl rest)
    where
      rest = Product (x' :| xs)
  Union xs -> Set.foldl (/\) u cs
    where
      cs = Set.map compl xs -- Either a set of base, or set of union of prods
      u = univ (dim s)

-- Set.fold (/\) (univ (dim s)) (compl `Set.map` xs)

baseIntersection :: Base -> Base -> Base
baseIntersection s s' = case (s, s') of
  (With x, With y) -> With $ IntSet.intersection x y
  (With x, Without y) -> With $ x IntSet.\\ y
  (Without x, With y) -> With $ y IntSet.\\ x
  (Without x, Without y) -> Without $  x <> y

(/\) :: Algebra -> Algebra -> Algebra
s /\ s' = assert (isValid s && isValid s' && dim s == dim s') $ case (s, s') of
  (_, _) | isEmpty s -> empty $ dim s
  (_, _) | isEmpty s' -> empty $ dim s'
  (_, _) | isUniv s -> s'
  (_, _) | isUniv s' -> s
  (Base x, Base y) -> Base $ baseIntersection x y
  (Union xs, Union ys) -> Union $ Set.map (uncurry (/\)) pairs
    where
      pairs = Set.cartesianProduct xs ys
  (Union xs, y) -> Union $ (/\ y) `Set.map` xs
  -- (Union (x :| []), y) -> x /\ y
  (Product (x :| []), y) -> x /\ y
  (x, Union ys) -> Union $ (x /\) `Set.map` ys
  -- (x, Union (y :| [])) -> x /\ y
  (x, Product (y :| [])) -> x /\ y
  --- Non-trivial Unions
  -- (28)
  -- (x, Union (y :| y' : ys)) -> (x /\ y) \/ (x /\ Union (y' :| ys))
  -- (29)
  -- (Union (x :| x' : xs), y) -> (x /\ y) \/ (Union (x' :| xs) /\ y)
  -- (32)
  --- Products (Now there are no unions!). Also, the assert makes sure the dimensions are equal, so just error in those cases (Basically, something non-product with something product)
  (Product (x :| x' : xs), Product (y :| y' : ys)) ->
    (x /\ y) >< (Product (x' :| xs) /\ Product (y' :| ys))
  (Base _, Product (_ :| _ : _)) -> error "Base inter dim>2"
  (Product (_ :| _ : _), Base _) -> error "dim>2 inter base"

baseUnion :: Base -> Base -> Base
baseUnion s s' = case (s, s') of
  (With x, With y) -> With $  x <> y
  (With x, Without y) -> Without $ y IntSet.\\ x
  (Without x, With y) -> Without $ x IntSet.\\ y
  (Without x, Without y) -> Without $ IntSet.intersection x y

(\/) :: Algebra -> Algebra -> Algebra
s \/ s' = assert (isValid s) $
  assert (isValid s) $
    assert (dim s == dim s') $
      case (s, s') of
        (_, _) | isEmpty s -> s'
        (_, _) | isEmpty s' -> s
        (_, _) | isUniv s -> univ (dim s)
        (_, _) | isUniv s' -> univ (dim s)
        (Base x, Base y) -> Base $ baseUnion x y
        -- Simplify single-products
        (Product (x :| []), y) -> x \/ y
        (x, Product (y :| [])) -> x \/ y
        (Union xs, Union ys) -> Union (xs <> ys)
        (Union xs, p@(Product _)) -> Union $ Set.insert p xs
        (p@(Product _), Union xs) -> Union $ Set.insert p xs
        (Union xs, b@(Base _)) -> Union $ Set.map (\/ b) xs
        (b@(Base _), Union xs) -> Union $ Set.map (b \/) xs
        -- Simplify singletons
        -- (x, Union (y :| [])) -> x \/ y
        ((Base _), Product (_ :| _ : _)) -> error "Base union dim>2"
        (Product (_ :| _ : _), (Base _)) -> error "dim>2 union Base"
        (x@(Product (_ :| _ : _)), y@(Product (_ :| _ : _))) -> Union $ Set.fromList [x, y]

(><) :: Algebra -> Algebra -> Algebra
s >< s' =
  -- trace (debugShow s ++ " >< " ++ debugShow s') $
  assert (isValid s && isValid s') $ case (s, s') of
    --- Simplify if argument empty (Nothing happens if univ)
    (_, _) | isEmpty s || isEmpty s' -> empty $ dim s + dim s'
    --- Base operations (figure 2)
    (x@(Base _), y@(Base _)) -> Product (x :| [y])
    --- Singleton simplifications
    (Union xs, Union ys) -> Union $ (\(x, y) -> x >< y) `Set.map` Set.cartesianProduct xs ys
    (Union xs, y@(Base _)) -> Union $ Set.map (>< y) xs
    (x@(Base _), Union ys) -> Union $ Set.map (x ><) ys
    (Union xs, y@(Product _)) -> Union $ Set.map (>< y) xs
    (x@(Product _), Union ys) -> Union $ Set.map (x ><) ys
    --- Non-trivial Unions
    -- (x@(Base _), Union (y :| y' : ys)) -> (x >< y) \/ (x >< Union (y' :| ys))
    -- (32)
    --- Products (Now there are no unions!)
    (Product xs@(_ :| _), Product ys@(_ :| _)) -> Product $ xs <> ys
    (x@(Base _), Product xs@(_ :| _)) -> Product $ x <| xs
    (Product xs@(_ :| _), x@(Base _)) -> Product $ NE.appendList xs [x]

---------------------------------------------------
-- FOL Query functions
---------------------------------------------------
--- Note that we only allow projections on dim > 2.
-- Helper-function
removeIndex :: Int -> NonEmpty a -> NonEmpty a
removeIndex i _ | i < 1 = error "removing non-positive index"
removeIndex _ (_ :| []) = error "removing index on dim=1 list"
removeIndex 1 (_ :| x : xs) = x :| xs
removeIndex i (x :| x' : xs) = x :| NE.toList (removeIndex (i - 1) (x' :| xs))

proj :: Int -> Algebra -> Algebra
proj i _ | i < 1 = error "non-positive projection"
proj i s | i > dim s = error "proj on i > dim"
proj _ (Base _) = error "base dim = 1, should be caught by other check"
proj 1 (Product (_ :| x : [])) = x
proj 2 (Product (x :| _ : [])) = x
proj i s = assert (isValid s) $ case s of
  Product xs -> Product (removeIndex i xs)
  Union xs -> Set.foldl (\/) e ps
    where
      ps = Set.map (proj i) xs
      e = empty (dim s - 1)

-- proj i (Union xs) = foldl (\/) empty (map (projProd i) xs)
---------------------------------------------------
-- PrettyShow implementation
---------------------------------------------------
instance  PrettyShow (Base) where
  pshow (With x) | IntSet.null x = "∅"
  pshow (With x) = pshow x
  pshow (Without x) | IntSet.null x = "𝕌"
  pshow (Without x) = pshow x ++ "ᶜ"

instance  PrettyShow (Algebra) where
  pshow (Base x) = pshow x
  pshow (Product xs) = withParens $ intercalate " × " (map pshow $ NE.toList xs)
  pshow (Union xs) = withParens $ intercalate " ∪ " (map pshow $ Set.toList xs)
