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

(\\) :: (Heyting a) => a -> a -> a
x \\ b = x /\ neg b

class Extra a where
  sym :: a -> a -> a

--- Difference
instance Extra Branches where
  -- Top \\ x = neg x
  -- _ \\ Top = bottom
  -- Drop xs \\ Drop ys = Drop $ IntMap.differenceWith (\x y -> properRel $ x \\ y) xs ys
  x `sym` y = case (x \\ y, y \\ x) of
    (Drop xs, Drop ys) -> Drop $ IntMap.union xs ys
    (Top, ys) -> neg ys
    (xs, Top) -> neg xs

instance Extra Wild where
  -- Bottom \\ _ = Bottom
  -- x \\ Bottom = x
  -- Lift x \\ Lift y = case properRel (x \\ y) of
  --   Nothing -> Bottom
  --   Just r -> Lift r

  x `sym` y = undefined

instance Extra Relation where
  -- Don't think this is right...
  -- r \\ s = case (wild r, wild s) of
  --   (Bottom, Bottom) -> r {branches = branches r \\ branches s}
  --   (_, _) -> r /\ neg s

  -- R {branches = xs, wild = v, dim = n} \\ R {branches = ys, wild = w, dim = m} =
  --   assert (n == m) $ R {branches = (xs \\ ys) `sym` (interWild ys w), wild = v \\ w, dim = n}

  r `sym` s = undefined
    where
      bs = branches r

symDiff :: IntMap a -> IntMap a -> IntMap a
x `symDiff` y = (x IntMap.\\ y) <> (y IntMap.\\ x)

symDiffLatt :: (Heyting a) => a -> a -> a
x `symDiffLatt` y = (neg x /\ y) \/ (x /\ neg y)

interWild :: Branches -> Wild -> Branches
interWild _ Bottom = bottom
interWild Top (Lift _) = error "Wildcard deeper than branches"
interWild (Drop xs) (Lift w) = Drop $ (IntMap.mapMaybe (`interMaybe` w) xs)
  where
    x `interMaybe` y = properRel $ x /\ y

--- If the branch-set is empty, propagate Nothing (that should only be allowed
--- for the top-level empty relation)
properRel :: Relation -> Maybe Relation
properRel R {branches = Drop xs}
  | null xs = Nothing
properRel r = Just r

-- sym :: (Heyting a) => a -> a -> a
-- x `sym` y = (x \\ y) \/ (y \\ x)

-- interDiff :: (Heyting b) => IntMap b -> Lifted b -> IntMap b
-- interDiff _ Bottom = bottom
-- interDiff xs (Lift w) = IntMap.map (\\ w) xs

instance Lattice (Relation) where
  r /\ s = assert (dim r == dim s) $ case (wild r, wild s) of
    (Bottom, Bottom) -> r {branches = branches r /\ branches s}
    (v, w) ->
      let
        xs = branches r
        ys = branches s
        newBranches = (xs /\ ys) `sym` interWild xs w `sym` interWild ys v
       in
        r {branches = newBranches, wild = v /\ w}

  -- R {wild = Bottom, branches = Top, dim = n} /\ R {wild = Bottom, branches = Top, dim = m} = assert (n == m) $ R {wild = Bottom, branches = Top, dim = n}
  -- R {wild = v, branches = xs, dim = n} /\ R {wild = w, branches = ys, dim = m} =
  --   R
  --     { wild = (v /\ w)
  --     , branches = (xs /\ ys) `sym` (xs `interWild` w) `sym` (ys `interWild` v)
  --     , dim = assert (n == m) n
  --     }
  --   where
  --     ysv = interWild ys v
  --     xsw = interWild xs w

  r@R {branches = xs, wild = Bottom, dim = n} \/ s@R {branches = ys, wild = Bottom} = R {branches = xs \/ ys, wild = Bottom, dim = n}
  -- r@R {branches = Top} \/ _ = r
  -- _ \/ s@R {branches = Top} = s
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
  neg r = case wild r of
    Bottom -> r {wild = top}
    Lift x | x == top -> r {wild = bottom}
    Lift x -> r {wild = Lift $ neg x}

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
-- Repl stuff
---------------------------------------------------
uuu :: (Relation)
uuu = finite [1, 2, 3]
vvv :: (Relation)
vvv = cofinite [2, 3, 4]

---------------------------------------------------
-- Pretty-printing
---------------------------------------------------
instance PrettyShow (Relation) where
  pshow (R {wild = Bottom, branches = Drop xs}) | null xs = "Ø"
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

instance PrettyShow (Branches) where
  pshow Top = "U"
  pshow (Drop x) = pshow x
