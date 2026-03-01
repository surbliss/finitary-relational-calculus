{-# LANGUAGE ExtendedDefaultRules #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Dict.Algebra where

import Algebra.Heyting
import Algebra.Lattice
import Algebra.Lattice.Dropped
import Algebra.Lattice.Lifted
import Control.Exception (assert)
import Text.Show qualified

import Data.IntMap.Strict qualified as IntMap

import PrettyShow
import Test.QuickCheck hiding ((><))

default (Int)

type Key = Int
type Wild = Lifted Relation
type Branches = Dropped (IntMap Relation)

data Relation
  = R
  { wild :: Lifted Relation
  , branches :: Dropped (IntMap Relation)
  , dim :: Nat
  }
  deriving (Show, Eq, Ord)

---------------------------------------------------
-- Lattice class instances
---------------------------------------------------
--- Difference
(\\) :: (Heyting a) => a -> a -> a
x \\ y = x /\ neg y

symDiff :: (PrettyShow a) => IntMap a -> IntMap a -> IntMap a
x `symDiff` y = (x IntMap.\\ y) <> (y IntMap.\\ x)

symDiffLatt :: (Heyting a) => a -> a -> a
x `symDiffLatt` y = (neg x /\ y) \/ (x /\ neg y)

interWild :: (Lattice b) => Dropped (IntMap b) -> Lifted b -> Dropped (IntMap b)
interWild _ Bottom = bottom
interWild Top (Lift _) = bug "Wildcard deeper than branches"
interWild (Drop xs) (Lift w) = Drop $ (IntMap.map (/\ w) xs)

sym :: (Heyting a) => a -> a -> a
x `sym` y = (x \\ y) \/ (y \\ x)

interDiff :: (Heyting b) => IntMap b -> Lifted b -> IntMap b
interDiff _ Bottom = bottom
interDiff xs (Lift w) = IntMap.map (\\ w) xs
instance Lattice (Relation) where
  R {wild = v, branches = xs, dim = n} /\ R {wild = w, branches = ys, dim = m} =
    R
      { wild = (v /\ w)
      , branches = (xs /\ ys) `sym` (xs `interWild` w) `sym` (ys `interWild` v)
      , dim = assert (n == m) n
      }

  x \/ y = undefined

-- R {wild = v, branches = xs, dim = nx} \/ R {wild = w, branches = ys, dim = ny} =
--   R {wild = wildUnion, branches = elemUnionv, dim = nx}
--   where
--     -- x@(R {}) \/ y@(R {}) = case (wild x, wild y) of
--     --   (Bottom, Bottom) -> R {branches = branches x \/ branches ys}
--     --   (Lift v, Bottom) -> R ()
--     -- R {wild = Bottom, branches = xs} \/ R {wild = Bottom, branches = ys} = R {wild = Bottom, branches = (xs \/ ys)}
--     -- R (Lift v) xs \/ R Bottom ys = R (Lift v) (interDiff xs (Lift v) \/ ys)
--     -- R Bottom xs \/ R (Lift w) ys = R (Lift w) (xs \/ interDiff ys (Lift w))
--     -- R v xs \/ R w ys = R wildUnion elemUnion -- FIX: Not correct yet

--     wildUnion = v \/ w
--     xs' = interDiff xs wildUnion
--     ys' = interDiff ys wildUnion
--     elemUnion = xs' \/ ys'

instance BoundedMeetSemiLattice (Branches) where
  top = Top

instance BoundedJoinSemiLattice (Branches) where
  bottom = Drop (bottom)

instance BoundedMeetSemiLattice (Wild) where
  top = Lift top

instance BoundedJoinSemiLattice (Wild) where
  bottom = Bottom

instance BoundedJoinSemiLattice (Relation) where
  bottom = R {branches = bottom, wild = Bottom, dim = 0}

instance BoundedMeetSemiLattice (Relation) where
  top = R {branches = top, wild = Bottom, dim = 0}

instance Heyting Branches where
  x ==> y = neg x \/ y
  neg Top = bottom
  neg (Drop xs) = Drop $ neg <$> xs

instance Heyting (Wild) where
  x ==> y = neg x \/ y
  neg Bottom = top
  neg (Lift x) = case neg x of
    R {wild = Bottom, branches = Top} -> top
    R {wild = Bottom, branches = xs} | null xs -> bottom
    y -> Lift y

instance Heyting (Relation) where
  x ==> y = neg x \/ y
  neg R {branches = Top, wild = Bottom, dim = n} = R {branches = bottom, wild = Bottom, dim = n}
  neg (x@R {}) = x {wild = neg (wild x)}

--- For retrieving
data Val = V Key | S deriving (Eq, Ord)
instance Show Val where
  show (V k) = show k
  show S = "*"

type Trie = [Val]

class ToIntSet a where
  toSet :: a -> IntSet

instance ToIntSet IntSet where
  toSet = id

instance ToIntSet [Int] where
  toSet = fromList

instance ToIntSet [Integer] where
  toSet = fromList . map fromIntegral

instance ToIntSet Int where
  toSet = one

instance ToIntSet Integer where
  toSet = one . fromIntegral

---------------------------------------------------
-- Exported functionality, reletional funcs
---------------------------------------------------
-- normalize :: (Relation) -> (Relation)
-- normalize (x@(R {})) = R {wild = normalizeWild (wild x), branches = normalizeIntMap}
--   where
--     normalizeIntMap = IntMap.filter (not . isEmpty) (IntMap.map normalize (branches x))

-- normalizeWild :: (Wild) -> (Wild)
-- normalizeWild (Lift xs) = case normalize xs of
--   xs' | isEmpty xs' -> Bottom
--   -- xs' | isUniv xs' -> Univ
--   xs' -> Lift xs'
-- normalizeWild u = u

-- (/\) :: (Relation) -> (Relation) -> (Relation)
-- Univ /\ x = x
-- x /\ Univ = x
-- (R (xs, v)) /\ (R (ys, w)) = R (IntMap.intersectionWith (/\) xs ys, v `intersectWild` w)

intersectWild :: (Wild) -> (Wild) -> (Wild)
x `intersectWild` Bottom = x
Bottom `intersectWild` x = x
Lift v `intersectWild` Lift w = Lift (v /\ w)

unionWild :: (Wild) -> (Wild) -> (Wild)
x `unionWild` Bottom = x
Bottom `unionWild` x = x
Lift v `unionWild` Lift w = Lift (v \/ w)

isEmpty :: (Relation) -> Bool
isEmpty R {wild = Bottom, branches = xs} = null xs
isEmpty _ = False

--- Exported for tests
dictEq :: (Relation) -> (Relation) -> Bool
dictEq x y = us == vs
  where
    vs = sort $ ordNub $ tries x
    us = sort $ ordNub $ tries y

---------------------------------------------------
-- Interface for interacting with Dicts
---------------------------------------------------
-- normalize :: (Relation) -> (Relation)
-- normalize Bottom = Bottom
-- normalize (R (xs, Univ)) = R (IntMap.map normalize xs, Univ)
-- normalize (R (xs, W ys)) = case (IntMap.map normalize xs, normalize ys) of
--   (xs', Univ) -> undefined

finite :: (ToIntSet a) => a -> (Relation)
finite x = R {wild = bottom, branches = Drop (IntMap.fromSet (\_ -> top) (toSet x)), dim = 1}

cofinite :: (ToIntSet a) => a -> (Relation)
cofinite x = R {wild = top, branches = Drop (IntMap.fromSet (\_ -> top) (toSet x)), dim = 1}

---------------------------------------------------
-- Testing help
---------------------------------------------------
tries :: (Relation) -> [Trie]
tries R {branches = Top} = [[S]]
tries (R {wild = w, branches = Drop xs}) = fins ++ wilds
  where
    fins = do
      (k, v) <- IntMap.assocs xs
      (V k :) <$> tries v
    wilds = case w of
      Bottom -> []
      Lift x -> (S :) <$> tries x

---------------------------------------------------
-- For assert-repl-testing
---------------------------------------------------
---------------------------------------------------
-- TRY 2: Helper-functions
---------------------------------------------------
lookupKey :: Key -> (Relation) -> Maybe (Relation)
lookupKey _ (R {branches = Top}) = Nothing
lookupKey k (R {branches = Drop xs}) = IntMap.lookup k xs

lookupWild :: (Relation) -> (Wild)
lookupWild (R {wild = Bottom}) = Bottom
lookupWild (R {wild = Lift w}) = Lift w

-- depth: How far down to 'Top'

-- depthsAll :: (Relation) -> [Int]
-- depthsAll R{wild=w, branches=xs, dim=n} = case (w, xs) of
--   where
--     depthsBranches
--   (Bottom, Top) -> [n]
--   (Lift w', Top) -> [n] <> depthsAll w'
--   ()

---------------------------------------------------
-- Generator + arbitrary
arbitraryRelIntMap :: Gen (IntMap (Relation))
arbitraryRelIntMap = do
  n <- chooseInt (0, 5)
  genRelIntMap n

--- Don't shrink into empties!
shrinkRelMap :: IntMap (Relation) -> [IntMap (Relation)]
shrinkRelMap xs = deletedKeys ++ shrunkElems
  where
    -- NOTE: Can also produce empty mapping
    deletedKeys = [IntMap.delete x xs | x <- IntMap.keys xs]
    shrunkElems =
      [ IntMap.insert x ys' xs
      | (x, ys) <- IntMap.assocs xs
      , ys' <- shrink ys
      -- , not (isEmpty ys') -- _But_ never allow binding a key to an empty map!
      ]

instance Arbitrary (Relation) where
  arbitrary = do
    n <- chooseInt (0, 5)
    genRel n

  shrink R {branches = Top, wild = Bottom} = []

-- shrink (R Bottom (xs)) = [R bottom (xs') | xs' <- shrinkRelMap xs]
-- shrink (R (Lift ys) (xs)) =
--   [R (Lift ys) (xs') | xs' <- shrinkRelMap xs]
--     ++ [R (Lift ys') (xs) | ys' <- shrink ys]
--     ++ [R bottom (xs)]
--     ++ shrinkElems (R (Lift ys) xs)
--     ++ shrinkWild (R (Lift ys) xs)

-- ++ [projLast (R (Lift ys) (xs))]

-- projElems :: (Relation) -> (Relation)
-- projElems Univ = Univ
-- projElems (R _ xs) | all (== Univ) xs = Univ
-- projElems (R w xs) = R w $ projElems <$> xs

shrinkElems :: (Relation) -> [(Relation)]
shrinkElems r@R {branches = xs}
  | null xs = []
  | all (== Top) xs = [Univ]
  | otherwise = r {branches = traverse shrinkElems xs}

shrinkWild :: (Relation) -> [(Relation)]
shrinkWild R {wild = Bottom} = []
shrinkWild R {wild = Lift (R {branches = Top})} = [top]
shrinkWild r = [r {wild = Lift w'} | w' <- shrinkWild (wild r)]

genRel :: Int -> Gen (Relation)
genRel n | n < 1 = pure univ
genRel n = do
  nKeys <- chooseInt (1, 5)
  keys <- vectorOf nKeys (arbitrary :: Gen Key)
  ds <- vectorOf nKeys $ genRel (n - 1)
  w <- genWild (n - 1)
  pure $ R w (IntMap.fromList (zip keys ds))

genWild :: Int -> Gen Wild
genWild n | n < 0 = pure Bottom
genWild n = Lift <$> genRel n

genRelIntMap :: Int -> Gen (IntMap (Relation))
genRelIntMap n | n < 1 = pure IntMap.empty
genRelIntMap n = do
  nKeys <- chooseInt (1, 5)
  keys <- vectorOf nKeys arbitrary
  vals <- vectorOf nKeys (frequency [(2, genRel (n - 1)), (1, pure univ)])
  pure $ fromList (zip keys vals)

---------------------------------------------------
-- Pretty-show implementations
---------------------------------------------------

instance PrettyShow (Relation) where
  pshow (R {wild = Bottom, branches = xs}) | null xs = "Ø"
  pshow (R {branches = Top}) = "U"
  pshow (R {wild = w, branches = Drop xs}) = "{" ++ elmArrs ++ pshow w ++ "}"
    where
      kvs = IntMap.assocs xs
      elmArrs = intercalate ", " $ map (\(x, y) -> pshow x ++ " -> " ++ pshow y) kvs
      -- TODO
      wArr = case w of
        Bottom -> ""
        Lift w' | isEmpty w' -> ""
        w' -> ", " ++ pshow w'

instance PrettyShow (Wild) where
  pshow Bottom = ""
  pshow (Lift a) = ", * -> " ++ pshow a

---------------------------------------------------
-- Repl stuff
---------------------------------------------------
uuu :: (Relation)
uuu = finite [1, 2, 3]
vvv :: (Relation)
vvv = cofinite [2, 3, 4]
