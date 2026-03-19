module Set.Algebra
where

import Control.Exception (assert)
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty ((:|)))
import Data.List.NonEmpty qualified as NE
import Data.Set (Set)
import Data.Set qualified as Set
import PrettyShow

--- Invariant to be maintained: IntSet is _never_ empty!
data Base = Empty | Univ | With IntSet | Without IntSet deriving (Eq, Show, Ord)

data Algebra where
  Base :: Base -> Algebra
  --- Always dim >= 2
  Times :: NonEmpty Algebra -> Algebra
  Union :: Set Algebra -> Algebra
  deriving (Eq, Show, Ord)

---------------------------------------------------
-- Exported
---------------------------------------------------
--- Exportings, to avoid super-many recursive 'simplify' calls
inter :: Algebra -> Algebra -> Algebra
inter x y = simplify $ x /\ y

union :: Algebra -> Algebra -> Algebra
union x y = simplify $ x \/ y

prod :: Algebra -> Algebra -> Algebra
prod x y = simplify $ x >< y

complement :: Algebra -> Algebra
complement = simplify . compl

--- Used by the exporteds
simplify :: Algebra -> Algebra
simplify s | isEmpty s = emptyA $ dim s
simplify s | isUniv s = univ $ dim s
simplify u@(Union xs) =
  let res = Set.filter (not . isEmpty) xs
   in if Set.null res then emptyA (dim u) else Union res
simplify s = s

--- Later: Use for asserts/tests
isSimple :: Algebra -> Bool
isSimple (Base Empty) = True
isSimple (Base Univ) = True
isSimple (Base (With x)) = isNonEmpty x
isSimple (Base (Without x)) = isNonEmpty x
isSimple (Times xs) = all isBase xs || all isSimple xs || all (not . isEmpty) xs
isSimple u@(Union xs) = all isTimes xs || all (== dim u) (Set.map dim xs) || all (not . isEmpty) xs || all (not . isUniv) xs
  where
    isTimes (Times _) = True
    isTimes _ = False

debugShow :: Algebra -> String
debugShow (Base Empty) = "Ø"
debugShow (Base Univ) = "𝕌"
debugShow (Base (With _)) = "F"
debugShow (Base (Without _)) = "C"
debugShow (Times xs) = "(P:" ++ show (debugShow <$> xs) ++ ")"
debugShow (Union xs) = "(U:" ++ show (debugShow `Set.map` xs) ++ ")"

---------------------------------------------------
-- ASSERTIONS: These are for assertions that data structure is represented correctly.
---------------------------------------------------
-- Can be removed, once this is tested thoroughly
-- This asserts that the current form is a normal form. That is, Base < Complement < Times < Union
-- At some point, it might make sense to move 'Complement' up

dim :: Algebra -> Int
dim (Base _) = 1
dim (Times xs) = length xs
dim (Union xs) = dim (Set.elemAt 0 xs) --- If simplified properly, will never be a null set

isBase :: Algebra -> Bool
isBase (Base _) = True
isBase _ = False

isValidTimes :: Algebra -> Bool
isValidTimes (Times xs) = all isBase xs
isValidTimes _ = False

isValidUnion :: Algebra -> Bool
isValidUnion s@(Union xs) =
  (dim s == 1 && all isBase xs) || (dim s > 1 && all isValidTimes xs)
isValidUnion _ = False

isValid :: Algebra -> Bool
isValid x = isBase x || isValidTimes x || isValidUnion x

---------------------------------------------------
-- Assertion stuff done
---------------------------------------------------

fins :: [Int] -> Algebra
fins [] = Base $ Empty
fins xs = Base $ With $ IntSet.fromList xs

emptyA :: Int -> Algebra
emptyA n | n < 1 = error "Non-positive univ"
emptyA 1 = Base Empty
emptyA n = Times (NE.fromList (replicate n (Base Empty)))

univ :: Int -> Algebra
univ n | n < 1 = error "Non-positive univ"
univ 1 = Base Univ
univ n = Times (NE.fromList (replicate n (Base Univ)))

isEmpty :: Algebra -> Bool
isEmpty s = case s of
  Base Empty -> True
  Base _ -> False
  Times xs -> any isEmpty xs
  Union xs -> all isEmpty xs

isUniv :: Algebra -> Bool
isUniv s = case s of
  Base Univ -> True
  Base _ -> False
  Times xs -> all isUniv xs
  Union xs -> any isUniv xs

--- All the below should return unions! So the types are consistent
--- Actually, nvm, lets try without! Just simplify as much as possible

isNonEmpty :: IntSet -> Bool
isNonEmpty s = not $ IntSet.null s

baseCompl :: Base -> Base
baseCompl Empty = Univ
baseCompl Univ = Empty
baseCompl (With x) = assert (isNonEmpty x) $ Without x
baseCompl (Without x) = assert (isNonEmpty x) $ With x

compl :: Algebra -> Algebra
compl s = case s of
  Base x -> Base $ baseCompl x
  Times (x :| []) -> compl x
  Times (x :| x' : xs) -> (compl x >< univ (1 + length xs)) \/ (univ 1 >< compl rest)
    where
      rest = Times (x' :| xs)
  Union xs -> Set.foldl (/\) u cs
    where
      cs = Set.map compl xs -- Either a set of base, or set of union of prods
      u = univ (dim s)

-- Makes sure sets are non-empty of base
normalizeBase :: Base -> Base
normalizeBase (With x) | IntSet.null x = Empty
normalizeBase (Without x) | IntSet.null x = Univ
normalizeBase x = x

baseIntersection :: Base -> Base -> Base
baseIntersection Empty _ = Empty
baseIntersection _ Empty = Empty
baseIntersection Univ x = x
baseIntersection x Univ = x
baseIntersection s s' = normalizeBase $
  case (s, s') of
    (With x, With y) -> With $ IntSet.intersection x y
    (With x, Without y) -> With $ x IntSet.\\ y
    (Without x, With y) -> With $ y IntSet.\\ x
    (Without x, Without y) -> Without $ x <> y

(/\) :: Algebra -> Algebra -> Algebra
s /\ s' =
  assert (dim s == dim s') $ case (s, s') of
    (_, _) | isEmpty s -> emptyA $ dim s
    (_, _) | isEmpty s' -> emptyA $ dim s'
    (_, _) | isUniv s -> s'
    (_, _) | isUniv s' -> s
    (Base x, Base y) -> Base $ baseIntersection x y
    --- Invariant: Unions never contain 'Univ', so no intersection can product 'Univ'. We should filter any empty-product out tho
    (Union xs, Union ys) -> Union $ Set.delete emptyProd inters
      where
        inters = Set.map (uncurry (/\)) pairs
        pairs = Set.cartesianProduct xs ys
        emptyProd = emptyA (dim s)
    (Union xs, y) -> Union $ (/\ y) `Set.map` xs
    (Times (x :| []), y) -> x /\ y
    (x, Union ys) -> Union $ (x /\) `Set.map` ys
    (x, Times (y :| [])) -> x /\ y
    --- Times (Now there are no unions!). Also, the assert makes sure the dimensions are equal, so just error in those cases (Basically, something non-product with something product)
    (Times (x :| x' : xs), Times (y :| y' : ys)) ->
      (x /\ y) >< (Times (x' :| xs) /\ Times (y' :| ys))
    (Base _, Times (_ :| _ : _)) -> error "Base inter dim>2"
    (Times (_ :| _ : _), Base _) -> error "dim>2 inter base"

baseUnion :: Base -> Base -> Base
baseUnion Empty x = x
baseUnion x Empty = x
baseUnion Univ _ = Univ
baseUnion _ Univ = Univ
baseUnion s s' = normalizeBase $ case (s, s') of
  (With x, With y) -> With $ x <> y
  (With x, Without y) -> Without $ y IntSet.\\ x
  (Without x, With y) -> Without $ x IntSet.\\ y
  (Without x, Without y) -> Without $ IntSet.intersection x y

(\/) :: Algebra -> Algebra -> Algebra
s \/ s' = case (s, s') of
  (_, _) | isEmpty s -> s'
  (_, _) | isEmpty s' -> s
  (_, _) | isUniv s -> univ (dim s)
  (_, _) | isUniv s' -> univ (dim s)
  (Base x, Base y) -> Base $ baseUnion x y
  -- Simplify single-products
  (Times (x :| []), y) -> x \/ y
  (x, Times (y :| [])) -> x \/ y
  (Union xs, Union ys) -> Union (xs <> ys)
  (Union xs, p@(Times _)) -> Union $ Set.insert p xs
  (p@(Times _), Union xs) -> Union $ Set.insert p xs
  (Union xs, b@(Base _)) -> Union $ Set.map (\/ b) xs
  (b@(Base _), Union xs) -> Union $ Set.map (b \/) xs
  -- Simplify singletons
  ((Base _), Times (_ :| _ : _)) -> error "Base union dim>2"
  (Times (_ :| _ : _), (Base _)) -> error "dim>2 union Base"
  (x@(Times (_ :| _ : _)), y@(Times (_ :| _ : _))) -> Union $ Set.fromList [x, y]

(><) :: Algebra -> Algebra -> Algebra
s >< s' =
  case (s, s') of
    --- Simplify if argument empty (Nothing happens if univ)
    (_, _) | isEmpty s || isEmpty s' -> emptyA $ dim s + dim s'
    --- Base operations (figure 2)
    (x@(Base _), y@(Base _)) -> Times (x :| [y])
    --- Singleton simplifications
    (Union xs, Union ys) -> Union $ (\(x, y) -> x >< y) `Set.map` Set.cartesianProduct xs ys
    (Union xs, y@(Base _)) -> Union $ Set.map (>< y) xs
    (x@(Base _), Union ys) -> Union $ Set.map (x ><) ys
    (Union xs, y@(Times _)) -> Union $ Set.map (>< y) xs
    (x@(Times _), Union ys) -> Union $ Set.map (x ><) ys
    --- Non-trivial Unions
    --- Timess (Now there are no unions!)
    (Times xs@(_ :| _), Times ys@(_ :| _)) -> Times $ xs <> ys
    (x@(Base _), Times (y :| ys)) -> Times $ x :| (y : ys)
    (Times xs@(_ :| _), x@(Base _)) -> Times $ NE.appendList xs [x]

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
proj 1 (Times (_ :| x : [])) = x
proj 2 (Times (x :| _ : [])) = x
proj i s = case s of
  Times xs -> Times (removeIndex i xs)
  Union xs -> Set.foldl (\/) e ps
    where
      ps = Set.map (proj i) xs
      e = emptyA (dim s - 1)

--- _Only_ for Bases, enforced through Term's smart-constructor
baseDiff :: Base -> Base -> Base
x `baseDiff` y = x `baseIntersection` (baseCompl y)

(\\) :: Algebra -> Algebra -> Algebra
Base x \\ Base y = Base $ x `baseDiff` y
_ \\ _ = error "Non-base intersection"

---------------------------------------------------
-- PrettyShow implementation
---------------------------------------------------
instance PrettyShow (Base) where
  pshow Empty = "∅"
  pshow (With x) = assert (isNonEmpty x) $ pshow x
  pshow Univ = "𝕌"
  pshow (Without x) = assert (isNonEmpty x) $ pshow x ++ "ᶜ"

instance PrettyShow (Algebra) where
  pshow (Base x) = pshow x
  pshow (Times xs) = withParens $ intercalate " × " (map pshow $ NE.toList xs)
  pshow (Union xs) = intercalate " ∪ " (map pshow $ Set.toList xs)
