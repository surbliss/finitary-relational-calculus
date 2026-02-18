{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Set.Query
where

import Data.IntMap (IntMap)
import Data.IntMap qualified as Map
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.List (intercalate)
import Data.Set (Set)
import Data.Set qualified as Set
import GHC.TypeLits

--- Invariant: With/Without _never_ contain the empty set!
data Base = With IntSet | Without IntSet deriving (Eq, Ord)
instance Show Base where
  show (With is) = "{" ++ intercalate ", " (show <$> IntSet.toAscList is) ++ "}"
  show (Without is) = "C{" ++ intercalate ", " (show <$> IntSet.toAscList is) ++ "}"

validBase :: Base -> Bool
validBase (With s) = not $ IntSet.null s
validBase (Without s) = not $ IntSet.null s

infixl 7 :/\
infixl 8 :\/
data Query where
  -- Nat = Dimension placement of the base.
  -- So, Base 2 X = 1 >< 1 >< X >< 1 >< ....
  Empty :: Query
  -- Univ :: Query
  Base :: Nat -> Base -> Query
  C :: Query -> Query -- Complement
  (:\/) :: Query -> Query -> Query
  (:/\) :: Query -> Query -> Query
  -- Proj :: [Nat] -> Query -> Query
  deriving (Eq, Show, Ord)

type Finitary = IntMap Int
type Union a = Set a

-- Type: Set (Union) of products (maps from dim->set of values).
newtype QTerm = QTerm (Union Finitary)

---------------------------------------------------
-- Helpers
---------------------------------------------------
-- qFin :: Dim -> Val -> Finitary
-- qFin d e = Map.fromAscList [(d, e)]

-- toTerm :: Query -> QTerm
-- toTerm Empty = QTerm Set.empty
-- toTerm (C Empty) = QTerm $ Set.singleton $ Map.empty
-- toTerm (C (Base n x)) = Base n $ complBase x
-- toTerm (C (C x)) = simp x
-- toTerm (Base n x :/\ Base m y) | n == m = Base n $ baseInter x y
-- toTerm (Base n x :\/ Base m y) | n == m = Base n $ baseUnion x y
-- toTerm (Base n x :/\ Base m y) = Base n x :/\ Base m y
-- toTerm (Base n x :\/ Base m y) = Base n x :\/ Base m y
-- toTerm (Base n x) = Base n x
-- --- Complements, Figure 3 (20-23)
-- toTerm (_ :/\ Empty) = Empty
-- toTerm (Empty :/\ _) = Empty
-- toTerm (x :\/ Empty) = simp x
-- toTerm (Empty :\/ x) = simp x
-- toTerm (x :/\ C Empty) = simp x
-- toTerm (C Empty :/\ x) = simp x
-- toTerm (_ :\/ C Empty) = C Empty
-- toTerm (C Empty :\/ _) = C Empty
-- toTerm (C (x :/\ y)) = simp $ C x :\/ C y
-- toTerm (C (x :\/ y)) = simp $ C x :/\ C y
-- toTerm (x :/\ (y :\/ z)) = simp $ (x :/\ y) :\/ (x :/\ z)
-- toTerm ((x :\/ y) :/\ z) = simp $ (x :/\ z) :\/ (y :/\ z)
-- toTerm (x :\/ y) = simp x :\/ simp y
-- toTerm (x :/\ y) = simp $ simp x :/\ simp y

fin :: Entry -> Query
fin (n, x) = Base n $ With $ IntSet.singleton x

fins :: Dim -> [Val] -> Query
fins n xs = Base n $ With $ IntSet.fromList xs

-- Implication
(-->) :: Query -> Query -> Query
x --> y = C x :\/ y

inter :: [Query] -> Query
inter [] = C Empty
inter (x : xs) = foldl (:/\) x xs

-- First arg: Base dim, increment for the rest. Only for repl testing
pairs :: Dim -> [(Val, Val)] -> Query
pairs _ [] = error "Empty pairs"
pairs n xs = foldl1 (:\/) dims
  where
    dims = map (\(x, y) -> fin (n, x) :/\ fin (n + 1, y)) xs

union :: [Query] -> Query
union [] = Empty
union (x : xs) = foldl (:\/) x xs

-- Tracks the dimension of the query
-- Pi :: Query (n + 2) -> Query (n + 1)

-- Delta :: Query (n+2) -> Query (n+1)
-- Sigma = rip

baseInter :: Base -> Base -> Base
baseInter (With x) (With y) = With $ IntSet.intersection x y
baseInter (With x) (Without y) = With $ x IntSet.\\ y
baseInter (Without x) (With y) = With $ y IntSet.\\ x
baseInter (Without x) (Without y) = Without $ x <> y

baseUnion :: Base -> Base -> Base
baseUnion (With x) (With y) = With $ x <> y
baseUnion (With x) (Without y) = Without $ y IntSet.\\ x
baseUnion (Without x) (With y) = Without $ x IntSet.\\ y
baseUnion (Without x) (Without y) = Without $ IntSet.intersection x y

-- First query is set of elements to check, whether they are in second query.
-- queryBase :: Int -> Query -> Bool
-- queryBase k (Base Empty) = False
-- queryBase k (Base Univ) = True
-- queryBase k (Base (With s)) = IntSet.member k s
-- queryBase k (Base (Without s)) = IntSet.notMember k s
-- queryBase k (C y) = not $ queryBase k y
-- queryBase _ _ = error "Should be impossible"
-- queryBase k (x :>< y) = error "Product should nenver be query 1"

isInBase :: Int -> Base -> Bool
isInBase k (With s) = IntSet.member k s
isInBase k (Without s) = IntSet.notMember k s

type Val = Int
type Dim = Nat
type Entry = (Dim, Val)

dim :: Entry -> Dim
dim (d, _) = d

val :: Entry -> Val
val (_, v) = v

proj :: Nat -> Query -> Query
proj i (Base n _) | n == i = C Empty
proj _ b@(Base _ (With xs)) | IntSet.null xs = b
proj _ b@(Base _ _) = b
proj _ Empty = Empty
proj _ (C Empty) = C Empty
proj i (x :/\ y) = proj i x :/\ proj i y
proj i (x :\/ y) = proj i x :\/ proj i y
proj i (C x) = proj i $ compl x

simp :: Query -> Query
simp Empty = Empty
simp (C Empty) = C Empty
simp (C (Base n x)) = Base n $ complBase x
simp (C (C x)) = simp x
simp (Base n x :/\ Base m y) | n == m = Base n $ baseInter x y
simp (Base n x :\/ Base m y) | n == m = Base n $ baseUnion x y
simp (Base n x :/\ Base m y) = Base n x :/\ Base m y
simp (Base n x :\/ Base m y) = Base n x :\/ Base m y
simp (Base n x) = Base n x
--- Complements, Figure 3 (20-23)
simp (_ :/\ Empty) = Empty
simp (Empty :/\ _) = Empty
simp (x :\/ Empty) = simp x
simp (Empty :\/ x) = simp x
simp (x :/\ C Empty) = simp x
simp (C Empty :/\ x) = simp x
simp (_ :\/ C Empty) = C Empty
simp (C Empty :\/ _) = C Empty
simp (C (x :/\ y)) = simp $ C x :\/ C y
simp (C (x :\/ y)) = simp $ C x :/\ C y
simp (x :/\ (y :\/ z)) = simp $ (x :/\ y) :\/ (x :/\ z)
simp ((x :\/ y) :/\ z) = simp $ (x :/\ z) :\/ (y :/\ z)
simp (x :\/ y) = simp x :\/ simp y
simp (x :/\ y) = simp $ simp x :/\ simp y

-- simp (Proj is (Base n _)) | n `elem` is = Empty
-- simp (Proj _ b@(Base _ _)) = b
-- simp (Proj _ Empty) = Empty
-- simp (Proj is (x :/\ y)) = simp (Proj is x :/\ Proj is y)
-- simp (Proj is (x :\/ y)) = simp (Proj is x :/\ Proj is y)
-- simp (Proj is (Proj js x)) = simp (Proj (is <> js) x)
-- simp (Proj i (C x)) = simp $ C (Proj i x)
-- simp (C (Proj i x)) = C (Proj i (simp x))

query :: [Entry] -> Query -> Bool
query xs q = all (`member` q) xs

-- compl Empty = C Empty
-- compl (C x) = x
-- compl (Base n x) = Base n $ complBase x
-- compl (x :\/ y) = C x :/\ C y
-- compl (x :/\ y) = C x :\/ C y

-- First arg = tuple, to check if is contained
member :: Entry -> Query -> Bool
member e@(i, k) s = case s of
  -- 1-arg constructors
  Empty -> False
  -- Univ -> True
  C x -> not $ member e x
  Base n x -> if i == n then k `isInBase` x else True
  -- Empty/Univ stuff
  x :/\ y -> member e x && member e y
  x :\/ y -> member e x || member e y

-- _ -> undefined

-- x :/\ Dim n y ->

-- (x :>< y) :/\ (z :>< w) -> query l $ (x :)

---------------------------------------------------
-- Helper functions
---------------------------------------------------
--- Invariant: dim q = n
-- For efficiency: Can just store this number in the datastructure later
-- dim :: Query -> Nat
-- dim (Base n x) = n
-- -- dim (x :>< y) = dim x + dim y
-- dim (C x) = dim x
-- dim (x :\/ y) = assert (dim x == dim y) $ dim x
-- dim (x :/\ y) = assert (dim x == dim y) $ dim x

-- univ n = Base Univ :>< univ (n - 1)
-- empty n = Base Empty :>< empty (n - 1)

compl :: Query -> Query
compl Empty = C Empty
compl (C x) = x
compl (Base n x) = Base n $ complBase x
compl (x :\/ y) = C x :/\ C y
compl (x :/\ y) = C x :\/ C y

-- compl (Proj i x) = Proj i $ compl x

complBase :: Base -> Base
complBase (With x) = Without x
complBase (Without x) = With x
