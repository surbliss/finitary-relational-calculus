{-# LANGUAGE ExtendedDefaultRules #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Dict.Algebra where

import Algebra.Heyting
import Algebra.Lattice
import Control.Exception (assert)
import Data.IntMap.Strict qualified as IntMap
import PrettyShow
import Test.QuickCheck hiding ((><))
import Text.Show qualified

default (Int)

type Key = Int

-- type Wild = Lifted Relation
-- type Branches = Dropped (IntMap Relation)

data Wild = None | W Relation deriving (Show, Eq, Ord)
data Branches = B (IntMap Relation) | End deriving (Show, Eq, Ord)

data Relation
  = R
  { wild :: Wild
  , branches :: Branches
  , dim :: Nat
  }
  deriving (Show, Eq, Ord)

---------------------------------------------------
-- Transformers for normalizing
---------------------------------------------------
--- These don't do recursive calls, just normalize one step down. So fine to use in other functions
toWild :: Relation -> Wild
toWild r
  | isEmpty r = None
  | otherwise = W r

bottomIfNull :: Wild -> Wild
bottomIfNull None = None
bottomIfNull (W xs)
  | isEmpty xs = None
  | otherwise = W xs

-- Transformer, to be applied to map functions. Makes functions return 'Nothing' if the resulting set Relation is empty, so it can be combined with 'IntMap.mapMaybe'
ifNotNull :: (Relation -> Relation) -> Relation -> Maybe Relation
ifNotNull f x
  | isEmpty res = Nothing
  | otherwise = Just res
  where
    res = f x

-- Only one layer down, so requires 'Wilds' to be normalized, i.e. no empty Lifts.
isEmpty :: Relation -> Bool
isEmpty R {branches = B xs, wild = None} = IntMap.null xs
isEmpty _ = False

-- Same here
isUniv :: Relation -> Bool
isUniv R {branches = End, wild = None} = True
isUniv R {branches = B xs, wild = W R {branches = End, wild = None}} = IntMap.null xs
isUniv _ = False

isEmptyBranches :: Branches -> Bool
isEmptyBranches End = False
isEmptyBranches (B xs) = IntMap.null xs

---------------------------------------------------
-- Lattice class instances
---------------------------------------------------

--- Branches
instance Lattice Branches where
  End /\ x = x
  x /\ End = x
  B xs /\ B ys = B $ IntMap.filter (not . isEmpty) $ IntMap.intersectionWith (/\) xs ys
  End \/ _ = End
  _ \/ End = End
  B xs \/ B ys = B $ IntMap.unionWith (normalizingUnion) xs ys
    where
      normalizingUnion x y = case x \/ y of
        r | isUniv r -> r {branches = End, wild = None}
        r -> r
instance BoundedJoinSemiLattice Branches where
  bottom = B IntMap.empty
instance BoundedMeetSemiLattice Branches where
  top = End
instance Heyting Branches where
  x ==> y = neg x \/ y -- TODO: More efficient version?
  neg End = bottom
  neg (B xs)
    | IntMap.null xs = End
    | otherwise = B $ neg <$> xs

--- Wild
instance Lattice Wild where
  None /\ _ = None
  _ /\ None = None
  W w /\ W v = case w /\ v of
    r | isEmpty r -> None
    r -> W r

  None \/ x = x
  x \/ None = x
  W w \/ W v = W $ case w \/ v of
    r | isUniv r -> r {branches = End, wild = None} -- not 'top' so dimension is kept
    r -> r

instance BoundedJoinSemiLattice Wild where
  bottom = None

instance BoundedMeetSemiLattice Wild where
  top = W top

instance Heyting (Wild) where
  x ==> y = neg x \/ y
  neg None = top
  neg (W x) = case neg x of
    r | isEmpty r -> bottom
    r -> W r

--- Relation
instance Lattice Relation where
  r /\ s = r {branches = resBranches, wild = resWild}
    where
      resWild = wild r /\ wild s
      resBranches =
        -- trace (show r <> "\n" <> show s) $
        (branches r /\ branches s)
          `sym` (branches r `interWild` wild s)
          `sym` (branches s `interWild` wild r)

  r@R {branches = xs, wild = None, dim = n} \/ R {branches = ys, wild = None} = r {branches = xs \/ ys, wild = None, dim = n}
  x \/ y = undefined

instance BoundedJoinSemiLattice (Relation) where
  bottom = R {branches = bottom, wild = None, dim = 0}

instance BoundedMeetSemiLattice (Relation) where
  top = R {branches = top, wild = None, dim = 0}

instance Heyting (Relation) where
  x ==> y = neg x \/ y

  -- neg r | isEmpty r = top
  neg r = r {wild = neg (wild r)}

-- case wild r of
--   None -> r {wild = top}
--   W x | x == top -> r {wild = bottom}
--   W x -> r {wild = W $ neg x}

(\\) :: (Heyting a) => a -> a -> a
x \\ y = x /\ neg y

sym :: (Heyting a) => a -> a -> a
x `sym` y = (x \\ y) \/ (y \\ x)

interWild :: Branches -> Wild -> Branches
interWild _ None = bottom
interWild End (W _) = top
interWild (B xs) (W w) = B $ (IntMap.mapMaybe (`interMaybe` w) xs)
  where
    x `interMaybe` y = properRel $ x /\ y

--- If the branch-set is empty, propagate Nothing (that should only be allowed
--- for the top-level empty relation)
properRel :: Relation -> Maybe Relation
properRel R {branches = B xs}
  | null xs = Nothing
properRel r = Just r

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
-- normalizeWild (W xs) = case normalize xs of
--   xs' | isEmpty xs' -> Bottom
--   -- xs' | isUniv xs' -> Univ
--   xs' -> W xs'
-- normalizeWild u = u

-- (/\) :: (Relation) -> (Relation) -> (Relation)
-- Univ /\ x = x
-- x /\ Univ = x
-- (R (xs, v)) /\ (R (ys, w)) = R (IntMap.intersectionWith (/\) xs ys, v `intersectWild` w)

intersectWild :: (Wild) -> (Wild) -> (Wild)
x `intersectWild` None = x
None `intersectWild` x = x
W v `intersectWild` W w = W (v /\ w)

unionWild :: (Wild) -> (Wild) -> (Wild)
x `unionWild` None = x
None `unionWild` x = x
W v `unionWild` W w = W (v \/ w)

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
-- normalize None= Bottom
-- normalize (R (xs, Univ)) = R (IntMap.map normalize xs, Univ)
-- normalize (R (xs, W ys)) = case (IntMap.map normalize xs, normalize ys) of
--   (xs', Univ) -> undefined

finite :: (ToIntSet a) => a -> (Relation)
finite x = R {wild = bottom, branches = B (IntMap.fromSet (\_ -> top) (toSet x)), dim = 1}

cofinite :: (ToIntSet a) => a -> (Relation)
cofinite x = R {wild = top, branches = B (IntMap.fromSet (\_ -> top) (toSet x)), dim = 1}

---------------------------------------------------
-- Testing help
---------------------------------------------------
tries :: (Relation) -> [Trie]
tries R {branches = End} = [[S]]
tries (R {wild = w, branches = B xs}) = fins ++ wilds
  where
    fins = do
      (k, v) <- IntMap.assocs xs
      (V k :) <$> tries v
    wilds = case w of
      None -> []
      W x -> (S :) <$> tries x

---------------------------------------------------
-- For assert-repl-testing
---------------------------------------------------
---------------------------------------------------
-- TRY 2: Helper-functions
---------------------------------------------------
lookupKey :: Key -> (Relation) -> Maybe (Relation)
lookupKey _ (R {branches = End}) = Nothing
lookupKey k (R {branches = B xs}) = IntMap.lookup k xs

lookupWild :: (Relation) -> (Wild)
lookupWild (R {wild = None}) = None
lookupWild (R {wild = W w}) = W w

-- depth: How far down to 'Top'

-- depthsAll :: (Relation) -> [Int]
-- depthsAll R{wild=w, branches=xs, dim=n} = case (w, xs) of
--   where
--     depthsBranches
--   (Bottom, Top) -> [n]
--   (W w', Top) -> [n] <> depthsAll w'
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
instance PrettyShow Relation where
  pshow (R {wild = None, branches = B xs}) | null xs = "Ø"
  pshow (R {branches = End}) = "U"
  pshow (R {wild = w, branches = B xs}) = "{" ++ elmArrs ++ pshow w ++ "}"
    where
      kvs = IntMap.assocs xs
      elmArrs = intercalate ", " $ map (\(x, y) -> pshow x ++ " -> " ++ pshow y) kvs

-- TODO

instance PrettyShow (Wild) where
  pshow None = ""
  pshow (W a) = ", * -> " ++ pshow a

instance PrettyShow (Branches) where
  pshow End = "U"
  pshow (B x) = pshow x

---------------------------------------------------
-- For testing
---------------------------------------------------
-- Remove all empty dead-ends
-- maybeNormal :: Relation -> Maybe Relation
-- maybeNormal r@R {branches = Top} = Just r
-- maybeNormal R {branches = Drop xs} | null xs = Nothing
-- maybeNormal r@R {branches = Drop xs} = Just $ r {branches = Drop (IntMap.map normalize xs)}

-- normalizeMaybe :: Relation -> Maybe Relation
-- normalizeMaybe R {branches = Drop xs, wild = Bottom} | IntMap.null xs = Nothing
-- normalizeMaybe r = case (newWild, newBranches) of
--   (Bottom, Drop xs) | IntMap.null xs -> Nothing
--   _ -> Just r {wild = newWild, branches = newBranches}
--   where
--     newWild = case wild r of
--       Bottom -> Bottom
--       Lift w -> case normalizeMaybe w of
--         Nothing -> Bottom
--         Just w' -> Lift w'
--     newBranches = case branches r of
--       Top -> Top
--       Drop xs -> Drop $ IntMap.mapMaybe normalizeMaybe xs

-- normalizeMaybe r@R {branches = Top, wild = Bottom} = Just r
-- normalizeMaybe r@R {branches = Top, wild = Lift w} = case normalizeMaybe w of
--   Just w' -> Just r {wild = Lift w'}
--   Nothing -> Just r {wild = bottom}

-- normalize :: Relation -> Relation
-- normalize r = case normalizeMaybe r of
--   Just x -> x
--   Nothing -> bottom

projLast :: Relation -> Relation
projLast r | isEmpty r = bottom
projLast R {dim = 1} = top
projLast r@R {branches = End, dim = n} = r {dim = n - 1}
projLast r@R {branches = B xs, wild = W w, dim = n} = r {branches = B $ IntMap.map projLast xs, wild = W $ projLast w, dim = n - 1}
projLast r@R {branches = B xs, wild = None, dim = n} = r {branches = B $ IntMap.map projLast xs, dim = n - 1}

---------------------------------------------------
-- Generator
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

  shrink r =
    [r {branches = xs} | xs <- shrinkBranches (branches r)]
      <> [r {wild = w} | w <- shrinkWild (wild r)]
      <> [projLast r]
      <> [s | B xs <- [branches r], s <- IntMap.elems xs]
      <> [w | W w <- [wild r]]

shrinkBranches :: Branches -> [Branches]
shrinkBranches End = []
shrinkBranches (B xs) = [End] ++ [B ys | ys <- shrink xs]

-- shrinkElems :: (Relation) -> [(Relation)]
-- shrinkElems r@R {branches = xs}
--   | null xs = []
--   | all (== Top) xs = [top]
--   | otherwise = r {branches = traverse shrinkElems xs}

shrinkWild :: Wild -> [Wild]
shrinkWild None = []
shrinkWild (W w) =
  [None]
    ++ [ W w'
       | w' <- shrink w
       , case branches w' of
           B xs -> not (IntMap.null xs)
           End -> True
       , not (wild w' == None)
       ]

---------------------------------------------------
genRel :: Int -> Gen (Relation)
genRel n | n < 1 = pure top
genRel n = do
  nKeys <- chooseInt (1, 5)
  keys <- vectorOf nKeys (arbitrary :: Gen Key)
  ds <- vectorOf nKeys $ genRel (n - 1)
  w <- genWild (n - 1)
  pure $ R {wild = w, branches = B (IntMap.fromList (zip keys ds)), dim = fromIntegral n}

genWild :: Int -> Gen Wild
genWild n | n < 0 = pure None
genWild n = W <$> genRel n

genRelIntMap :: Int -> Gen (IntMap (Relation))
genRelIntMap n | n < 1 = pure IntMap.empty
genRelIntMap n = do
  nKeys <- chooseInt (1, 5)
  keys <- vectorOf nKeys arbitrary
  vals <- vectorOf nKeys (frequency [(2, genRel (n - 1)), (1, pure top)])
  pure $ fromList (zip keys vals)

---------------------------------------------------
-- Functions for tests
---------------------------------------------------
hasNoEmpty :: Relation -> Bool
hasNoEmpty R {branches = B xs} | IntMap.null xs = False
hasNoEmpty R {branches = B xs, wild = W w} = hasNoEmpty w && all hasNoEmpty xs
hasNoEmpty R {branches = B xs} = all hasNoEmpty xs
hasNoEmpty R {wild = W w} = hasNoEmpty w
hasNoEmpty _ = True
