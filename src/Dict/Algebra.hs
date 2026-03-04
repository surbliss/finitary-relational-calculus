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
data Wild = None | W Relation | Univ deriving (Show, Eq, Ord)
newtype Branches = B (IntMap Relation) deriving (Show, Eq, Ord)

data Relation
  = R
  { wild :: Wild
  , branches :: Branches
  , dim :: Nat
  }
  deriving (Eq, Ord)

instance Show Relation where
  show = pshow

---------------------------------------------------
-- Transformers for normalizing
---------------------------------------------------

{- | Helpers to simplify the data-structures, i.e. normalize empty/univs.
Should _not_ do recursive calls, so they are safe to use multiple times.
-}
class Simplifiable a where
  simplify :: a -> a

instance Simplifiable Wild where
  simplify None = bottom
  simplify Univ = top
  simplify (W r)
    | isEmpty r = bottom
    | isUniv r = top
    | otherwise = W r

instance Simplifiable Branches where
  simplify (B xs) = B $ IntMap.filter (not . isEmpty) xs

instance Simplifiable Relation where
  simplify r = r {branches = simplify (branches r), wild = simplify (wild r)}

-- Only one layer down, so requires 'Wilds' to be normalized, i.e. no empty Lifts.
isEmpty :: Relation -> Bool
isEmpty R {branches = B xs, wild = None} = IntMap.null xs
isEmpty _ = False

-- Same here
isUniv :: Relation -> Bool
isUniv R {branches = B xs, wild = Univ} = IntMap.null xs
isUniv _ = False

---------------------------------------------------
-- Bonus-classes
---------------------------------------------------
class SymDiff a where
  (\\) :: a -> a -> a
  sym :: a -> a -> a

instance SymDiff Wild where
  x \\ y = x /\ neg y
  x `sym` y = (x \\ y) \/ (y \\ x)

instance SymDiff Relation where
  x \\ y = x /\ neg y
  x `sym` y = (x \\ y) \/ (y \\ x)

--- As we can't negate Branches, need specific implementation here!
instance SymDiff Branches where
  B xs \\ B ys = simplify $ B $ IntMap.differenceWith (nonEmptyDiff) xs ys
    where
      x `nonEmptyDiff` y = case (x \\ y) of
        r
          | isEmpty r -> Nothing
          | otherwise -> Just r

  -- x `sym` y = (x \\ y) \/ (y \\ x)
  x `sym` y = simplify $ B $ IntMap.unionWith (\/) xs ys
    where
      B xs = (x \\ y)
      B ys = (y \\ x)

---------------------------------------------------
-- Lattice class instances
---------------------------------------------------
--- Lattice
instance Lattice Branches where
  B xs /\ B ys = simplify $ B $ IntMap.intersectionWith (/\) xs ys
  B xs \/ B ys = simplify $ B $ IntMap.unionWith (\/) xs ys

instance Lattice Wild where
  None /\ _ = None
  _ /\ None = None
  Univ /\ x = x
  x /\ Univ = x
  W w /\ W v = simplify $ W $ w /\ v

  None \/ x = x
  x \/ None = x
  Univ \/ _ = Univ
  _ \/ Univ = Univ
  W w \/ W v = W $ case w \/ v of
    r | isUniv r -> r {branches = bottom, wild = top} -- not plain 'top' so dimension is kept
    r -> r

instance Lattice Relation where
  r /\ s = r {branches = resBranches, wild = resWild}
    where
      resWild = wild r /\ wild s
      resBranches =
        -- trace (show r <> "\n" <> show s) $
        (branches r /\ branches s)
          `sym` (branches r `interWild` wild s)
          `sym` (branches s `interWild` wild r)

  -- PERF: Most certainly not the most efficient implementation, but works for now
  r \/ s = neg (neg r /\ neg s)

--- Bounded _ SemiLattice
instance BoundedJoinSemiLattice Branches where
  bottom = B IntMap.empty

instance BoundedJoinSemiLattice Wild where
  bottom = None

instance BoundedMeetSemiLattice Wild where
  top = Univ

--- Heyting
instance Heyting (Wild) where
  x ==> y = neg x \/ y
  neg None = top
  neg Univ = bottom
  neg (W x) = case neg x of
    r | isEmpty r -> bottom
    r -> W r
instance Heyting (Relation) where
  x ==> y = neg x \/ y
  neg r = r {wild = neg (wild r)}

-- r@R {branches = xs, wild = None, dim = n} \/ R {branches = ys, wild = None} = r {branches = xs \/ ys, wild = None, dim = n}
-- x \/ y = undefined

instance BoundedJoinSemiLattice (Relation) where
  bottom = R {branches = bottom, wild = bottom, dim = 0}

instance BoundedMeetSemiLattice (Relation) where
  top = R {branches = bottom, wild = top, dim = 0}

-- case wild r of
--   None -> r {wild = top}
--   W x | x == top -> r {wild = bottom}
--   W x -> r {wild = W $ neg x}

interWild :: Branches -> Wild -> Branches
interWild _ None = bottom
interWild x Univ = x
interWild (B xs) (W w) = B $ (IntMap.mapMaybe (`interMaybe` w) xs)
  where
    x `interMaybe` y = properRel $ x /\ y
    properRel R {branches = B ys}
      | null ys = Nothing
    properRel r = Just r

mapWild :: (Relation -> Relation) -> Wild -> Wild
mapWild _ None = None
mapWild _ Univ = Univ
mapWild f (W w) = simplify $ W (f w)

mapBranches :: (Relation -> Relation) -> Branches -> Branches
mapBranches f (B xs) = simplify $ B $ f <$> xs

--- Cartesial product
(><) :: Relation -> Relation -> Relation
r >< s
  | isEmpty r = r {dim = dim r + dim s}
  | isEmpty s = s {dim = dim r + dim s}
  | dim r == 0 && isUniv r = s
  | isUniv r = case wild r of {}
  | otherwise = r {branches = mapBranches (>< s) (branches r), wild = mapWild (>< s) (wild r), dim = dim r + dim s}

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
-- Interface for interacting with Dicts
---------------------------------------------------
finite :: (ToIntSet a) => a -> (Relation)
finite x = R {wild = bottom, branches = B (IntMap.fromSet (\_ -> top) (toSet x)), dim = 1}

cofinite :: (ToIntSet a) => a -> (Relation)
cofinite x = R {wild = top, branches = B (IntMap.fromSet (\_ -> top) (toSet x)), dim = 1}

--- Finite pairs
pairs :: [(Int, Int)] -> Relation
pairs xs = R {dim = 2, wild = None, branches = B $ IntMap.fromList $ map mkRelation xs}
  where
    mkRelation (x, y) = (x, (finite y))

---------------------------------------------------
-- Testing help
---------------------------------------------------
tries :: (Relation) -> [Trie]
tries R {branches = B xs, wild = Univ} | IntMap.null xs = [[S]]
tries (R {wild = w, branches = B xs}) = fins ++ wilds
  where
    fins = do
      (k, v) <- IntMap.assocs xs
      (V k :) <$> tries v
    wilds = case w of
      None -> []
      Univ -> [[S]]
      W x -> (S :) <$> tries x

eq :: Relation -> Relation -> Bool
r `eq` s = sortNub (tries r) == sortNub (tries s)

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
  pshow r
    | isUniv r = "U"
    | isEmpty r = "Ø"
    | otherwise = "{" <> pshow (branches r) <> pshow (wild r) <> "}"

instance PrettyShow Wild where
  pshow w = case w of
    None -> ""
    Univ -> ", * -> U"
    W a -> ", * -> " <> pshow a

instance PrettyShow Branches where
  -- pshow End = "U"
  pshow (B x) =
    intercalate ", " $
      IntMap.assocs x
        <&> ( \(k, r) ->
                if isUniv r then pshow k else pshow k <> " -> " <> pshow r
            )

---------------------------------------------------
-- For testing
---------------------------------------------------

---------------------------------------------------
-- Generator
---------------------------------------------------
--- Newtype wrappers to enforce consistent dims for pairs and triples of relations
newtype Relation2 = Rel2 (Relation, Relation) deriving (Show, Eq, Ord)
newtype Relation3 = Rel3 (Relation, Relation, Relation) deriving (Show, Eq, Ord)

instance Arbitrary (Relation) where
  arbitrary = do
    n <- chooseInt (0, 5)
    genRelation n

  shrink r = shrinkRelSameDim r <> shrinkRelDecreaseDim r

instance Arbitrary Relation2 where
  arbitrary = do
    n <- chooseInt (0, 5)
    r <- genRelation n
    s <- genRelation n
    pure $ Rel2 (r, s)

  shrink (Rel2 (r, s)) =
    [Rel2 (r', s) | r' <- shrinkRelSameDim r]
      <> [Rel2 (r, s') | s' <- shrinkRelSameDim s]
      <> [Rel2 (r', s') | r' <- shrinkRelDecreaseDim r, s' <- shrinkRelDecreaseDim s]

instance Arbitrary Relation3 where
  arbitrary = do
    n <- chooseInt (0, 5)
    r <- genRelation n
    s <- genRelation n
    u <- genRelation n
    pure $ Rel3 (r, s, u)

  shrink (Rel3 (r, s, u)) =
    [Rel3 (r', s, u) | r' <- shrinkRelSameDim r]
      <> [Rel3 (r, s', u) | s' <- shrinkRelSameDim s]
      <> [Rel3 (r, s, u') | u' <- shrinkRelSameDim u]
      <> [ Rel3 (r', s', u')
         | r' <- shrinkRelDecreaseDim r
         , s' <- shrinkRelDecreaseDim s
         , u' <- shrinkRelDecreaseDim u
         ]

--- Generator functions
-- For generator: n > 0 should always produce something non-empty!
genWild :: Int -> Gen Wild
genWild 1 = pure top
genWild n = do
  r <- genRelation (n - 1)
  pure $ simplify $ W r

genBranches :: Int -> Gen Branches
genBranches n = do
  numKeys <- chooseInt (1, 5)
  ps <- replicateM numKeys $ do
    k <- arbitrary
    v <- case n of
      0 -> error "Too small branch n"
      1 -> pure top
      _ -> genRelation (n - 1)
    pure (k, v)
  pure $ simplify $ B $ IntMap.fromList ps

genRelationScaled :: Int -> Gen Relation
genRelationScaled n = genRelation (n `mod` 15)

genRelation :: Int -> Gen Relation
genRelation 0 = oneof [pure bottom, pure top]
genRelation n = do
  (xs, w) <-
    oneof $
      [ (,) <$> genBranches n <*> pure bottom
      , (,) <$> pure bottom <*> genWild n
      , (,) <$> genBranches n <*> genWild n
      ]
  pure $ simplify R {branches = xs, wild = w, dim = fromIntegral n}

--- Shrinking functions
shrinkWild :: Wild -> [Wild]
shrinkWild None = []
shrinkWild Univ = [None]
shrinkWild (W w) = [simplify $ W w' | w' <- shrinkRelSameDim w]

shrinkWildDecreaseDim :: Wild -> [Wild]
shrinkWildDecreaseDim None = [None]
shrinkWildDecreaseDim Univ = [Univ]
shrinkWildDecreaseDim (W w) = [simplify $ W w' | w' <- shrinkRelDecreaseDim w]

-- shrinkWild (W w) = [W w' | w' <- shrink w, not (isEmpty w)]

shrinkBranches :: Branches -> [Branches]
shrinkBranches (B xs) = deleteKey
  where
    deleteKey = [B (IntMap.delete x xs) | x <- IntMap.keys xs]
    shrinkKeys = [B (IntMap.insert x (simplify v') xs) | (x, v) <- IntMap.assocs xs, v' <- shrinkRelSameDim v]

-- shrinkVal = [B $ IntMap.insert k v' xs | (k, v) <- IntMap.assocs xs, v' <- shrink v, not (isEmpty v')]

shrinkRelSameDim :: Relation -> [Relation]
shrinkRelSameDim r = branchShrinks <> wildShrinks
  where
    branchShrinks = do
      xs <- shrinkBranches (branches r)
      pure $ r {branches = xs}
    wildShrinks = do
      w <- shrinkWild (wild r)
      pure r {wild = w}

shrinkRelDecreaseDim :: Relation -> [Relation]
shrinkRelDecreaseDim R {dim = 0} = []
shrinkRelDecreaseDim R {dim = 1} = [bottom, top]
shrinkRelDecreaseDim r
  | isUniv r || isEmpty r = [r {dim = dim r - 1}]
shrinkRelDecreaseDim r = nextWild <> nextBranches <> [cutLastDim r]
  where
    B xs = branches r
    nextBranches = IntMap.elems xs
    nextWild = case wild r of
      None -> []
      Univ -> []
      W w -> [w]

cutLastDim :: Relation -> Relation
cutLastDim R {dim = 0} = error "Don't cut last dim of dim 0 pls"
cutLastDim r@R {dim = 1}
  | isEmpty r = bottom
  | otherwise = top
cutLastDim r@R {branches = B xs, dim = n} = case wild r of
  None -> r {branches = simplify $ B $ cutLastDim <$> xs, dim = n - 1}
  Univ -> r {branches = simplify $ B $ cutLastDim <$> xs, dim = n - 1}
  W w ->
    r
      { branches = simplify $ B $ cutLastDim <$> xs
      , wild = simplify $ W $ cutLastDim w
      , dim = n - 1
      }

---------------------------------------------------
-- Functions for tests
---------------------------------------------------
hasNoEmpty :: Relation -> Bool
hasNoEmpty r
  | isEmpty r = False
  | isUniv r = True
hasNoEmpty R {branches = B xs, wild = w} = case w of
  Univ -> all hasNoEmpty xs
  None -> not (IntMap.null xs) && all hasNoEmpty xs
  W v -> all hasNoEmpty xs && hasNoEmpty v
