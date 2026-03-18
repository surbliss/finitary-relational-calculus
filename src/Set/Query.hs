{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Set.Query
where

import Text.Show qualified

import Data.IntSet qualified as IntSet

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
  Empty :: Query
  Base :: Nat -> Base -> Query
  C :: Query -> Query -- Complement
  (:\/) :: Query -> Query -> Query
  (:/\) :: Query -> Query -> Query
  deriving (Eq, Show, Ord)

type Finitary = IntMap Int
type Union a = Set a

-- Type: Set (Union) of products (maps from dim->set of values).
newtype QTerm = QTerm (Union Finitary)

---------------------------------------------------
-- Helpers
---------------------------------------------------
fin :: Entry -> Query
fin (n, x) = Base n $ With $ IntSet.singleton x

fins :: Dim -> [Val] -> Query
fins n xs = Base n $ With $ IntSet.fromList xs

-- Implication
(-->) :: Query -> Query -> Query
x --> y = C x :\/ y

inter :: [Query] -> Query
inter [] = C Empty
inter (x : xs) = foldr (:/\) x xs

-- First arg: Base dim, increment for the rest. Only for repl testing
pairs :: Dim -> [(Val, Val)] -> Query
pairs _ [] = error "Empty pairs"
pairs n xs = foldr (:\/) d1 dims
  where
    d1 = case dims of
      [] -> error "oh no"
      d : _ -> d
    dims = map (\(x, y) -> fin (n, x) :/\ fin (n + 1, y)) xs

union :: [Query] -> Query
union [] = Empty
union (x : xs) = foldr (:\/) x xs

-- Tracks the dimension of the query
-- Pi :: Query (n + 2) -> Query (n + 1)

-- Delta :: Query (n+2) -> Query (n+1)

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

query :: [Entry] -> Query -> Bool
query xs q = all (`member` q) xs

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

---------------------------------------------------
-- Helper functions
---------------------------------------------------
compl :: Query -> Query
compl Empty = C Empty
compl (C x) = x
compl (Base n x) = Base n $ complBase x
compl (x :\/ y) = C x :/\ C y
compl (x :/\ y) = C x :\/ C y

complBase :: Base -> Base
complBase (With x) = Without x
complBase (Without x) = With x
