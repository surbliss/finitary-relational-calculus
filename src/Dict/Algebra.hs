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
  , depth :: Nat -- To avoid traversing, when converting to None
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
  simplify None = None
  simplify Univ = Univ
  simplify (W R {branches = B xs, wild = None})
    | IntMap.null xs = None
  simplify (W r) = W r -- Keep W Univ!

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
isUniv R {branches = B xs, wild = Univ, depth = n} =
  assert
    (n == 0 && IntMap.null xs)
    True
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
  W w \/ W v = W $ w \/ v

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
  neg R {branches = B xs, wild = None, depth = 0} = assert (IntMap.null xs) top
  neg r@R {wild = None, depth = n} = r {wild = W (univN (n - 1))}
  neg r = r {wild = neg (wild r)}

-- r@R {branches = xs, wild = None, dim = n} \/ R {branches = ys, wild = None} = r {branches = xs \/ ys, wild = None, dim = n}
-- x \/ y = undefined

instance BoundedJoinSemiLattice (Relation) where
  -- _Mathematically_ depth 0 would probably be more appropriate here, but it would never be able to be used, as we should only intersect/union things of same dim.
  bottom = R {branches = bottom, wild = bottom, depth = 0}

instance BoundedMeetSemiLattice (Relation) where
  top = R {branches = bottom, wild = top, depth = 0}

emptyN :: Nat -> Relation
emptyN n | n < 0 = error "Negative dimension for emptyN"
emptyN n = R {branches = B IntMap.empty, wild = None, depth = n}

univN :: Nat -> Relation
univN n | n < 0 = error "Negative dimension for univN"
univN 0 = top
univN n = R {branches = B IntMap.empty, wild = W (univN (n - 1)), depth = n}

interWild :: Branches -> Wild -> Branches
interWild _ None = bottom
interWild x Univ = x
interWild (B xs) (W w) = B $ (IntMap.map (/\ w) xs)

-- where
--   x `interMaybe` y = properRel $ x /\ y
--   properRel R {branches = B ys} | IntMap.null ys = Nothing
--   properRel r = Just r

mapWild :: (Relation -> Relation) -> Wild -> Wild
mapWild _ None = None
mapWild _ Univ = Univ
mapWild f (W w) = simplify $ W (f w)

mapBranches :: (Relation -> Relation) -> Branches -> Branches
mapBranches f (B xs) = simplify $ B $ f <$> xs

class Extendable a where
  (><) :: a -> Relation -> a

instance Extendable Branches where
  B xs >< r = simplify $ B $ xs <&> (>< r)

instance Extendable Relation where
  r >< s | isEmpty r || isEmpty s = emptyN (depth r + depth s)
  R {branches = B xs, wild = Univ, depth = n} >< s =
    assert (IntMap.null xs && n == 0) $
      s
  r >< s = case (wild r) of
    None -> r {branches = branches r >< s, depth = depth r + depth s}
    W w -> r {branches = branches r >< s, wild = W (w >< s), depth = depth r + depth s}
    Univ -> error "Should not be possible to have Univ here"

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
finite x = R {wild = bottom, branches = B (IntMap.fromSet (\_ -> top) (toSet x)), depth = 1}

cofinite :: (ToIntSet a) => a -> (Relation)
cofinite x = R {wild = W top, branches = B (IntMap.fromSet (\_ -> top) (toSet x)), depth = 1}

--- Finite pairs
pairs :: [(Int, Int)] -> Relation
pairs xs = R {depth = 2, wild = None, branches = B $ IntMap.fromListWith (\/) $ map mkRelation xs}
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
xxx :: Relation
xxx = uuu
yyy :: Relation
yyy = finite [2, 3, 4]
xss :: IntMap Relation
B xss = branches xxx
yss :: IntMap Relation
B yss = branches yyy
vvv = cofinite [2, 3, 4]

---------------------------------------------------
-- Pretty-printing
---------------------------------------------------
instance PrettyShow Relation where
  pshow r
    | isUniv r = "U" -- Always dim 1
    | isEmpty r = "Ø-" <> show (depth r)
    | otherwise = "{" <> intercalate ", " pretties <> "}"
    where
      pretties = prettyBranches (branches r) <> prettyWild (wild r)
      prettyBranches (B xs) = xs & IntMap.toList <&> prettyMap
      prettyMap (k, v) = pshow k <> " -> " <> pshow v
      prettyWild None = []
      prettyWild Univ = ["* -> U"]
      prettyWild (W w) = ["* -> " <> pshow w]

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
        <&> (\(k, r) -> pshow k <> " -> " <> pshow r)

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
genWild n | n < 1 = error "<1 genBranches "
genWild 0 = pure top
genWild n = do
  r <- genRelation (n - 1)
  pure $ simplify $ W r

genBranches :: Int -> Gen Branches
genBranches n
  | n < 1 = error "<1 genBranches"
  | otherwise = do
      numKeys <- chooseInt (1, 5)
      ps <- replicateM numKeys $ do
        k <- arbitrary
        v <- case n of
          0 -> error "Too small branch n"
          1 -> pure top
          _ -> genRelation (n - 1)
        pure (k, v)
      pure $ simplify $ B $ IntMap.fromList ps

--- Only generate non-empty? Maybe?
genRelation :: Int -> Gen Relation
genRelation n | n < 0 = error "Non-positive dim"
genRelation 0 = oneof [pure bottom, pure top]
genRelation n = do
  (xs, w) <-
    oneof $
      [ (,) <$> genBranches n <*> pure bottom
      , (,) <$> pure bottom <*> genWild n
      , (,) <$> genBranches n <*> genWild n
      ]
  pure $ simplify R {branches = xs, wild = w, depth = fromIntegral n}

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

-- shrinkKeys = [B (IntMap.insert x (simplify v') xs) | (x, v) <- IntMap.assocs xs, v' <- shrinkRelSameDim v]

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
shrinkRelDecreaseDim R {depth = 0} = []
shrinkRelDecreaseDim R {depth = 1} = [bottom, top]
shrinkRelDecreaseDim r | isEmpty r = [r {depth = depth r - 1}]
shrinkRelDecreaseDim r = nextWild <> nextBranches
  where
    -- <> [cutLastDim r]

    B xs = branches r
    nextBranches = IntMap.elems xs
    nextWild = case wild r of
      None -> []
      Univ -> []
      W w -> [w]

-- cutLastDim :: Relation -> Relation
-- cutLastDim R {depth = 0} = error "Don't cut last dim of dim 0 pls"
-- cutLastDim r@R {depth = 1}
--   | isEmpty r = bottom
--   | otherwise = top
-- cutLastDim r@R {branches = B xs, depth = n} = case wild r of
--   None -> r {branches = simplify $ B $ cutLastDim <$> xs, depth = n - 1}
--   Univ -> r {branches = simplify $ B $ cutLastDim <$> xs, depth = n - 1}
--   W w ->
--     r
--       { branches = simplify $ B $ cutLastDim <$> xs
--       , wild = simplify $ W $ cutLastDim w
--       , depth = n - 1
--       }

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
