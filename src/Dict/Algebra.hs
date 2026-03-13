{-# LANGUAGE ExtendedDefaultRules #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Dict.Algebra where

-- import Algebra.Heyting
-- import Algebra.Lattice
import Control.Exception (assert)
import Data.IntMap.Strict qualified as IntMap
import PrettyShow
import Test.QuickCheck hiding (getSize, (><))
import Text.Show qualified

type Key = Int
data Wild = None | W Relation | Univ deriving (Show, Eq, Ord)
type Branches = IntMap Relation

data Relation
  = R
  { wild :: Wild
  , branches :: Branches
  , depth :: Nat -- To avoid traversing, when converting to None
  , size :: Nat -- number of keys
  }
  deriving (Eq, Ord)

instance Show Relation where
  show = pshow

---------------------------------------------------
-- Transformer-classes for normalizing
---------------------------------------------------
class Algebra a where
  -- Intersection, Symmetric difference, Union, Difference
  (/\), (\/), (<+>), (\\) :: a -> a -> a

  -- Identity for <+> and \/, annihilator for /\
  empt :: a

class Negatable a where
  neg :: a -> a -- Complement
  univ :: a -- = neg empt

-- Cartesian product
class Extendable a where
  (><) :: a -> Relation -> a

---------------------------------------------------
-- Instantiation of classes
---------------------------------------------------
instance Algebra Branches where
  xs \\ ys = IntMap.differenceWith (\x y -> nonEmptyRelation $ x \\ y) xs ys

  -- x \\ y and y \\ x must be disjoint, so we are free to combine the branches
  -- with <+> or \/.
  x <+> y = IntMap.unionWith (\/) (x \\ y) (y \\ x)
  xs /\ ys = removeEmptyBranches $ IntMap.intersectionWith (<+>) xs ys
  xs \/ ys = IntMap.unionWith (\/) xs ys

  empt = IntMap.empty

instance Algebra Wild where
  None /\ _ = empt
  _ /\ None = empt
  Univ /\ x = x
  x /\ Univ = x
  W w /\ W v = nonEmptyWild (w /\ v)

  None \/ x = x
  x \/ None = x
  Univ \/ _ = univ
  _ \/ Univ = univ
  W w \/ W v = W $ w \/ v

  x \\ y = x /\ neg y

  x <+> y = (x \\ y) \/ (y \\ x)

  empt = None

instance Negatable Wild where
  univ = Univ

  neg None = univ
  neg Univ = empt
  neg (W x) = nonEmptyWild (neg x)

instance Algebra Relation where
  -- Optimization: If both wildcards are empty, then only iterate over the
  -- set with the fewest number of keys.
  r@R {wild = None} /\ s@R {wild = None} = r {branches = resBranches, size = getSize resBranches}
    where
      -- x: smallest of the relations
      (rmin, smax) = if size r < size s then (r, s) else (s, r)
      updateBranch x rx = IntMap.lookup x (branches smax) <&> (rx /\) >>= nonEmptyRelation
      resBranches = IntMap.mapMaybeWithKey updateBranch (branches rmin)
  r@R {wild = None} /\ s = r {branches = resBranches, size = getSize resBranches}
    where
      updateBranch x rx = nonEmptyRelation $ case IntMap.lookup x (branches s) of
        Nothing -> case wild s of
          None -> error "Should be handled by case above"
          Univ -> rx
          W w -> rx /\ w
        Just sy -> rx /\ (sy `symWild` (wild s))
      resBranches = IntMap.mapMaybeWithKey updateBranch (branches r)
  r /\ s@R {wild = None} = s {branches = resBranches, size = getSize resBranches}
    where
      bx = branches r
      by = branches s
      updateBranch y ry = nonEmptyRelation $ case IntMap.lookup y bx of
        Nothing -> case (wild r) of
          None -> error "Should be handled by case above"
          Univ -> ry
          W w -> ry /\ w
        Just rx -> (rx `symWild` wild r) /\ ry
      resBranches = IntMap.mapMaybeWithKey updateBranch by
  r /\ s = r {branches = resBranches, wild = wild r /\ wild s, size = getSize resBranches}
    where
      resBranches =
        (branches r /\ branches s)
          <+> (branches r `interWild` wild s)
          <+> (branches s `interWild` wild r)

  -- PERF: Most certainly not the most efficient implementation, but works for now
  r \/ s = neg (neg r /\ neg s)
  x <+> y = (x \\ y) \/ (y \\ x)

  x \\ y = x /\ neg y
  empt = R {branches = empt, wild = empt, depth = 0, size = 0}

instance Negatable Relation where
  neg R {branches = xs, wild = None, depth = 0} = assert (IntMap.null xs) univ
  neg r@R {wild = None, depth = n} = r {wild = W (univN (n - 1))}
  neg r = r {wild = neg (wild r)}

  univ = R {branches = empt, wild = univ, depth = 0, size = 0}

instance Extendable Branches where
  xs >< r
    | isEmptyRelation r = empt
    | otherwise = xs <&> (>< r)

instance Extendable Relation where
  r >< s | isEmptyRelation r || isEmptyRelation s = emptyN (depth r + depth s)
  R {branches = xs, wild = Univ, depth = n} >< s =
    assert (IntMap.null xs && n == 0) $
      s
  r >< s = case (wild r) of
    None -> r {branches = branches r >< s, depth = depth r + depth s}
    W w -> r {branches = branches r >< s, wild = W (w >< s), depth = depth r + depth s}
    Univ -> error "Should not be possible to have Univ here"

---------------------------------------------------
-- Helper-functions
---------------------------------------------------

{- | Simplifies the data-structures, by removing maps to empty relations
Note that these only ever checks _one_ level down, so they are save to use
inside recursive definitions.
-}
isEmptyRelation :: Relation -> Bool
isEmptyRelation R {branches = xs, wild = None} = IntMap.null xs
isEmptyRelation _ = False

-- For use with Maybe-maps from IntMap
nonEmptyRelation :: Relation -> Maybe Relation
nonEmptyRelation r
  | isEmptyRelation r = Nothing
  | otherwise = Just r

nonEmptyWild :: Relation -> Wild
nonEmptyWild r
  | isEmptyRelation r = None
  | otherwise = W r

removeEmptyBranches :: Branches -> Branches
removeEmptyBranches xs = IntMap.filter (not . isEmptyRelation) xs

-- | Update the count of branches - use after op that might modify these
getSize :: Branches -> Nat
getSize bs = fromIntegral $ IntMap.size bs

updateSize :: Relation -> Relation
updateSize r = r {size = getSize (branches r)}

-- WRONG: Attempt at projection, but _wrong_: Projection over symmetric difference is
-- more complicated than this
projLast :: Relation -> Relation
projLast R {depth = 0} = empt
projLast r@R {depth = 1}
  | isEmptyRelation r = empt
  | otherwise = univ
projLast r@R {branches = xs, depth = n} =
  r
    { branches = projLast <$> xs
    , wild = newWild
    , depth = n - 1
    }
  where
    newWild = case wild r of
      None -> None
      Univ -> Univ
      W w -> W (projLast w)

emptyN :: Nat -> Relation
emptyN n | n < 0 = error "Negative dimension for emptyN"
emptyN n = R {branches = IntMap.empty, wild = None, depth = n, size = 0}

univN :: Nat -> Relation
univN n | n < 0 = error "Negative dimension for univN"
univN 0 = univ
univN n = R {branches = IntMap.empty, wild = W (univN (n - 1)), depth = n, size = 0}

interWild :: Branches -> Wild -> Branches
interWild _ None = empt
interWild x Univ = x
interWild xs (W w) = IntMap.map (/\ w) xs

symWild :: Relation -> Wild -> Relation
symWild r None = r
symWild r Univ = neg r
symWild r (W w) = r <+> w

---------------------------------------------------
-- Printing and checking
---------------------------------------------------

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
finite x = R {wild = empt, branches = bs, depth = 1, size = getSize bs}
  where
    bs = IntMap.fromSet (\_ -> univ :: Relation) (toSet x)

cofinite :: (ToIntSet a) => a -> (Relation)
cofinite x = R {wild = W univ, branches = bs, depth = 1, size = getSize bs}
  where
    bs = IntMap.fromSet (\_ -> univ :: Relation) (toSet x)

--- Finite pairs
pairs :: [(Int, Int)] -> Relation
pairs xs = R {depth = 2, wild = None, branches = bs, size = getSize bs}
  where
    mkRelation (x, y) = (x, (finite y))
    bs = IntMap.fromListWith (\/) $ map mkRelation xs

triples :: [(Int, Int, Int)] -> Relation
triples xs = foldr (\/) (emptyN 3) [finite [x] >< finite [y] >< finite [z] | (x, y, z) <- xs]

---------------------------------------------------
-- Pretty-printing
---------------------------------------------------
showSize :: Relation -> String
showSize r = "|" <> show (size r) <> "|"

-- Same here
isUniv :: Relation -> Bool
isUniv R {branches = xs, wild = Univ, depth = n} =
  assert
    (n == 0 && IntMap.null xs)
    True
isUniv _ = False
instance PrettyShow Relation where
  pshow r
    | isUniv r && size r /= 0 = "oh no, univ wrong size!" <> show (size r)
    | isUniv r = "U" -- Always dim 1
    | isEmptyRelation r && size r /= 0 = "oh no, empty wrong size!" <> show (size r)
    | isEmptyRelation r = show (depth r) <> "Ø"
    | otherwise = showSize r <> "{" <> intercalate ", " pretties <> "}"
    where
      pretties = prettyBranches (branches r) <> prettyWild (wild r)
      prettyBranches xs = xs & IntMap.toList <&> prettyMap
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
  pshow x =
    intercalate ", " $
      IntMap.assocs x
        <&> (\(k, r) -> pshow k <> " -> " <> pshow r)

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
genWild 0 = pure univ
genWild n = do
  r <- genRelation (n - 1)
  pure $ nonEmptyWild r

genBranches :: Int -> Gen Branches
genBranches n
  | n < 1 = error "<1 genBranches"
  | otherwise = do
      numKeys <- chooseInt (1, 5)
      ps <- replicateM numKeys $ do
        k <- arbitrary
        v <- case n of
          0 -> error "Too small branch n"
          1 -> pure univ
          _ -> genRelation (n - 1)
        pure (k, v)
      pure $ IntMap.fromList ps

--- Only generate non-empty? Maybe?
genRelation :: Int -> Gen Relation
genRelation n | n < 0 = error "Non-positive dim"
genRelation 0 = oneof [pure empt, pure univ]
genRelation n = do
  (xs, w) <-
    oneof $
      [ (,) <$> genBranches n <*> pure empt
      , (,) <$> pure empt <*> genWild n
      , (,) <$> genBranches n <*> genWild n
      ]
  pure $ R {branches = xs, wild = w, depth = fromIntegral n, size = getSize xs}

--- Shrinking functions
shrinkWild :: Wild -> [Wild]
shrinkWild None = []
shrinkWild Univ = [None]
shrinkWild (W w) = [nonEmptyWild w' | w' <- shrinkRelSameDim w]

shrinkWildDecreaseDim :: Wild -> [Wild]
shrinkWildDecreaseDim None = [None]
shrinkWildDecreaseDim Univ = [Univ]
shrinkWildDecreaseDim (W w) = [nonEmptyWild w' | w' <- shrinkRelDecreaseDim w]

-- shrinkWild (W w) = [W w' | w' <- shrink w, not (isEmptyRelation w)]

shrinkBranches :: Branches -> [Branches]
shrinkBranches xs = deleteKey
  where
    deleteKey = [IntMap.delete x xs | x <- IntMap.keys xs]

-- shrinkKeys = [B (IntMap.insert x (removeEmpty v') xs) | (x, v) <- IntMap.assocs xs, v' <- shrinkRelSameDim v]

-- shrinkVal = [B $ IntMap.insert k v' xs | (k, v) <- IntMap.assocs xs, v' <- shrink v, not (isEmptyRelation v')]

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
shrinkRelDecreaseDim R {depth = 1} = [empt, univ]
shrinkRelDecreaseDim r | isEmptyRelation r = [r {depth = depth r - 1}]
shrinkRelDecreaseDim r = nextWild <> nextBranches
  where
    -- <> [cutLastDim r]

    xs = branches r
    nextBranches = IntMap.elems xs
    nextWild = case wild r of
      None -> []
      Univ -> []
      W w -> [w]

-- cutLastDim :: Relation -> Relation
-- cutLastDim R {depth = 0} = error "Don't cut last dim of dim 0 pls"
-- cutLastDim r@R {depth = 1}
--   | isEmptyRelation r = empt
--   | otherwise = univ
-- cutLastDim r@R {branches = B xs, depth = n} = case wild r of
--   None -> r {branches = removeEmpty $ B $ cutLastDim <$> xs, depth = n - 1}
--   Univ -> r {branches = removeEmpty $ B $ cutLastDim <$> xs, depth = n - 1}
--   W w ->
--     r
--       { branches = removeEmpty $ B $ cutLastDim <$> xs
--       , wild = removeEmpty $ W $ cutLastDim w
--       , depth = n - 1
--       }

---------------------------------------------------
-- Functions for tests
---------------------------------------------------
hasEmpty :: Relation -> Bool
hasEmpty r
  | isEmptyRelation r = True
  | isUniv r = False
hasEmpty R {branches = xs, wild = w} = case w of
  Univ -> any hasEmpty xs
  None -> IntMap.null xs || any hasEmpty xs
  W v -> any hasEmpty xs || hasEmpty v
tries :: (Relation) -> [Trie]
tries R {branches = xs, wild = Univ} | IntMap.null xs = [[S]]
tries (R {wild = w, branches = xs}) = fins ++ wilds
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
