{-# LANGUAGE ExtendedDefaultRules #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Dict.Algebra (
  --- For use
  Algebra (..),
  Extendable (..),
  Relation,
  emptyRelN,
  univRelN,
  neg,
  finite,
  cofinite,
  pairs,
  triples,
  --- For testing
  dim,
  Relation1 (Rel1),
  Relation2 (Rel2),
  Relation3 (Rel3),
  hasEmpty,
  isEmptyRelation,
  countRel,
  --- For Term generator
  genRelation,
  shrinkRelSameDim,
) where

import Control.Exception (assert)
import Control.Monad (guard)
import Data.Function ((&))
import Data.Functor ((<&>))
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.List (intercalate)
import PrettyShow
import Test.QuickCheck hiding ((><))

--- Types
type Relation = (Branches, Wild, Int) -- Relation with its depth
type Wild = Maybe Node
type Branches = (IntMap Node, Int) -- Map with its size
data Node = N Relation | End deriving (Show, Eq, Ord)

---------------------------------------------------
-- Dictionary-helpers
---------------------------------------------------

dim :: Relation -> Int
dim (_, _, n) = n

count :: Branches -> Int
count (_, i) = i

countRel :: Relation -> Int
countRel (xs, _, _) = count xs

-- Just computes the size, and adds that
branches :: IntMap Node -> Branches
branches xs = (xs, IntMap.size xs)

---------------------------------------------------
-- Functions for transforming relations
---------------------------------------------------
--- Typeclass to implement on all data-types
class Algebra a where
  -- Intersection, Symmetric difference, Union, Difference
  (/\), (\/), (<+>), (\\) :: a -> a -> a

  -- Identity for <+> and \/, annihilator for /\
  empty :: a

-- Cartesian product
class Extendable a where
  (><) :: a -> Relation -> a

-- Extra functions for relations
neg :: Relation -> Relation -- Complement
neg (_, _, n) | n < 1 = error "Can't negate non-positive-dim"
neg (xs, Nothing, n) = (xs, Just ((univN (n - 1))), n)
neg (xs, Just End, n) = assert (n == 1) (xs, Nothing, n)
neg (xs, Just (N x), n) = (xs, nonEmpty (N (neg x)), n)

univN :: Int -> Node
univN n | n < 0 = error "Negative dimension for univN"
univN 0 = End
univN n = N (empty, Just (univN (n - 1)), n)

univRelN :: Int -> Relation
univRelN n = (empty, Just (univN (n - 1)), n)

---------------------------------------------------
-- Instantiation of classes
---------------------------------------------------
instance Algebra Branches where
  (xs, _) \\ (ys, _) = branches $ IntMap.differenceWith (\x y -> nonEmpty $ x \\ y) xs ys

  -- x \\ y and y \\ x must be disjoint, so we are free to combine the branches
  -- with <+> or \/.
  (xs, _) <+> (ys, _) = removeEmpty $ IntMap.unionWith (<+>) xs ys
  (xs, n) /\ (ys, m)
    | n < m = combineWith xs ys
    | otherwise = combineWith ys xs
    where
      combineWith as bs = branches $ IntMap.mapMaybeWithKey (comb bs) as
      comb bs a ra = case (IntMap.lookup a bs) of
        Nothing -> Nothing
        Just rb -> nonEmpty (ra /\ rb)

  (xs, _) \/ (ys, _) = branches $ IntMap.unionWith (\/) xs ys

  empty = (IntMap.empty, 0)

instance Algebra Wild where
  Nothing /\ _ = empty
  _ /\ Nothing = empty
  Just w /\ Just v = nonEmpty (w /\ v)

  Nothing \/ x = x
  x \/ Nothing = x
  Just w \/ Just v = nonEmpty (w \/ v)

  Nothing \\ _ = empty
  x \\ Nothing = x
  Just x \\ Just y = nonEmpty $ x \\ y

  Nothing <+> y = y
  y <+> Nothing = y
  Just x <+> Just y = nonEmpty $ x <+> y

  empty = Nothing

-- Note: Wild _can't_ be negated, because we don't know how deep 'Empty' is outside of a relation!

-- Q: Should we assert only End with End here?
instance Algebra Node where
  End /\ End = End
  End /\ _ = error "/\\ Right node deeper"
  _ /\ End = error "/\\ Left node deeper"
  N r /\ N s = N (r /\ s)

  End \/ End = End
  End \/ _ = error "\\/ Right node deeper"
  _ \/ End = error "\\/ Left node deeper"
  N r \/ N s = N (r \/ s)

  End \\ End = empty
  End \\ _ = error "\\\\ Right node deeper"
  _ \\ End = error "\\\\ Left node deeper"
  N x \\ N y = N (x \\ y)

  End <+> End = empty
  End <+> _ = error "<+> Right node deeper"
  _ <+> End = error "<+> Left node deeper"
  N x <+> N y = N (x <+> y)

  empty = N empty

instance Algebra Relation where
  -- Optimization: If both wildcards are empty, then only iterate over the
  -- set with the fewest number of keys.
  (xs, v, n) /\ (ys, w, m) = assert (n == m) $ case (v, w) of
    (Nothing, Nothing) -> (xs /\ ys, Nothing, n)
    (Nothing, Just y) -> (interSym xs ys y, Nothing, n)
    (Just x, Nothing) -> (interSym ys xs x, Nothing, n)
    (Just x, Just y)
      | count xs < count ys -> (interSym xs ys y <+> inter ys x, v /\ w, n)
      | otherwise -> (inter xs y <+> interSym ys xs x, v /\ w, n)

  (bs, v, n) <+> (cs, w, m) = assert (n == m) $ (bs <+> cs, v <+> w, n)

  -- If not rewriting useing other rules, then we have to explicitly factor out between branches and wild, like for /\.
  r \/ s = neg (neg r /\ neg s)
  x \\ y = x /\ neg y

  empty = (empty, empty, 1)

--- For all these: Only do the 'isEmptyRelation' check in the actual relation definition
instance Extendable Branches where
  (xs, n) >< r = (xs <&> (>< r), n)

instance Extendable Node where
  End >< r = N r
  N s >< r
    | isEmptyRelation s = empty
    | otherwise = N (s >< r)

instance Extendable Wild where
  Nothing >< _ = Nothing
  Just w >< r = Just (w >< r)

instance Extendable Relation where
  (xs, Nothing, n) >< (_, _, m) | isEmptyBranches xs = (empty, empty, n + m)
  (_, _, n) >< (ys, Nothing, m) | isEmptyBranches ys = (empty, empty, n + m)
  (xs, v, n) >< r@(_, _, m) = (xs >< r, v >< r, n + m)

---------------------------------------------------
-- Helper-functions
---------------------------------------------------

--- Some helper-functions for Algebra Relation instance below:
-- Lookup x into first branch, and compute x /\ (y + w) if  present
interSym :: Branches -> Branches -> Node -> Branches
interSym (xs, _) (ys, _) wy = branches $ IntMap.mapMaybeWithKey comb xs
  where
    comb x ra = case (ra, IntMap.lookup x ys) of
      (End, Nothing) -> Just wy
      (End, Just rx) -> nonEmpty $ (rx <+> wy)
      (_, Nothing) -> nonEmpty (ra /\ wy)
      (_, Just rx) -> nonEmpty $ ra /\ (rx <+> wy)

-- Lookup x into first branch, and compute x /\ y if  present
inter :: Branches -> Node -> Branches
inter (xs, _) y = branches $ IntMap.mapMaybe (\x -> nonEmpty (x /\ y)) xs

{- | Simplifies the data-structures, by removing maps to empty relations
Note that these only ever checks _one_ level down, so they are save to use
inside recursive definitions.
-}
isEmptyBranches :: Branches -> Bool
isEmptyBranches (xs, n)
  | n == 0 = assert (IntMap.null xs) True
  | otherwise = False

isEmptyRelation :: Relation -> Bool
isEmptyRelation (xs, Nothing, _) = isEmptyBranches xs
isEmptyRelation _ = False

isEmpty :: Node -> Bool
isEmpty End = False
isEmpty (N x) = isEmptyRelation x

nonEmpty :: Node -> Maybe Node
nonEmpty x | isEmpty x = Nothing | otherwise = Just x

removeEmpty :: IntMap Node -> Branches
removeEmpty xs = branches $ IntMap.filter (not . isEmpty) xs

---------------------------------------------------
-- Interface for interacting with Dicts
---------------------------------------------------
finite :: [Int] -> Relation
finite xs = (branches bs, empty, 1)
  where
    assocs = [(i, End) | i <- xs]
    bs = IntMap.fromList assocs

cofinite :: [Int] -> Relation
cofinite xs = (branches bs, Just End, 1)
  where
    assocs = [(i, End) | i <- xs]
    bs = IntMap.fromList assocs

--- Finite pairs
pairs :: [(Int, Int)] -> Relation
pairs xs = (branches bs, empty, 2)
  where
    mkRelation (x, y) = (x, N (finite [y]))
    bs = IntMap.fromListWith (\/) $ map mkRelation xs

triples :: [(Int, Int, Int)] -> Relation
triples xs = foldr (\/) (empty >< empty >< empty) [finite [x] >< (finite [y]) >< (finite [z]) | (x, y, z) <- xs]

---------------------------------------------------
-- Pretty-printing
---------------------------------------------------
instance PrettyShow Node where
  pshow End = "E"
  pshow (N r)
    | isEmptyRelation r = "Ø"
    | otherwise = pshow r

instance PrettyShow Relation where
  pshow r@(_, _, 1) = "{" ++ intercalate ", " (keysAndWild r) ++ "}"
  pshow (bs, Nothing, _) = "{" ++ pshow bs ++ "}"
  pshow (bs, w, _) | isEmptyBranches bs = "{" ++ pshow w ++ "}"
  pshow (bs, w, _) = "{" ++ pshow bs ++ ", " ++ pshow w ++ "}"

keysAndWild :: Relation -> [String]
keysAndWild ((bs, _), Nothing, _) | IntMap.null bs = []
keysAndWild ((bs, _), w, _) | IntMap.null bs = [pshow w]
keysAndWild ((bs, _), Nothing, _) = pshow <$> IntMap.keys bs
keysAndWild ((bs, _), w@(Just _), _) = (pshow <$> IntMap.keys bs) <> [pshow w]

instance PrettyShow Branches where
  pshow (xs, _) = xs & IntMap.toAscList & map pshowBranch & intercalate ", "
    where
      pshowBranch (x, rx) = show x ++ " -> " ++ pshow rx

instance PrettyShow Wild where
  pshow w = case w of
    Nothing -> ""
    Just End -> "*"
    Just a -> "* -> " <> pshow a

---------------------------------------------------
-- Generator
---------------------------------------------------
--- Newtype wrappers to enforce consistent dims for pairs and triples of relations
newtype Relation1 = Rel1 (Relation) deriving (Show, Eq, Ord)
newtype Relation2 = Rel2 (Relation, Relation) deriving (Show, Eq, Ord)
newtype Relation3 = Rel3 (Relation, Relation, Relation) deriving (Show, Eq, Ord)

instance PrettyShow Relation1 where
  pshow (Rel1 r) = pshow r

getLayers :: Gen Int
getLayers = do
  chooseInt (1, 10)

instance Arbitrary (Relation1) where
  arbitrary = do
    layers <- getLayers
    rel <- genRelation layers
    pure $ Rel1 rel

  shrink (Rel1 r) = Rel1 <$> (shrinkRelSameDim r <> shrinkRelDecreaseDim r)

instance Arbitrary Relation2 where
  arbitrary = do
    layers <- getLayers
    r <- genRelation layers
    s <- genRelation layers
    pure $ Rel2 (r, s)

  shrink (Rel2 (r, s)) =
    [Rel2 (r', s) | r' <- shrinkRelSameDim r]
      <> [Rel2 (r, s') | s' <- shrinkRelSameDim s]
      <> [Rel2 (r', s') | r' <- shrinkRelDecreaseDim r, s' <- shrinkRelDecreaseDim s]

instance Arbitrary Relation3 where
  arbitrary = do
    layers <- getLayers
    r <- genRelation layers
    s <- genRelation layers
    u <- genRelation layers
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
genWild n | n < 1 = error "genWild on non-positive"
genWild n = do
  r <- genNode (n - 1)
  pure $ Just r

genBranches :: Int -> Gen Branches
genBranches n | n < 1 = error "genBranches on non-positive"
genBranches n = do
  size <- getSize
  branchCount <- chooseInt (1, max 1 $ (floor . sqrt . fromIntegral) size)
  let branchSize = size `div` branchCount
  rs <- vectorOf branchCount $ resize branchSize $ genNode (n - 1)
  pure $ branches $ IntMap.fromList $ zip [1 .. branchCount] rs

--- Only generate non-empty? Maybe?
genRelation :: Int -> Gen Relation
genRelation n | n < 1 = error "genRelation on non-positive"
genRelation n = sized $ \size -> case size of
  1 -> pure (empty, Just (univN (n - 1)), n)
  _ -> do
    (xs, w) <-
      oneof $
        [ (,) <$> genBranches n <*> pure empty
        , (,) <$> pure empty <*> genWild n
        , (,) <$> resize (size `div` 2) (genBranches n) <*> resize (size `div` 2) (genWild n)
        ]
    pure (xs, w, n)

-- Only generate non-empty nodes!
genNode :: Int -> Gen Node
genNode n | n < 0 = error "genNode on negative"
genNode 0 = pure End
genNode n = sized $ \size -> case size of
  1 -> pure $ (univN n)
  _ -> do
    r <- genRelation n
    pure $ N r

--- Shrinking functions
shrinkWild :: Wild -> [Wild]
shrinkWild Nothing = []
shrinkWild (Just w) = [nonEmpty w' | w' <- shrinkNodeSameDim w]

shrinkBranchesSameDim :: Branches -> [Branches]
shrinkBranchesSameDim (_, 0) = []
shrinkBranchesSameDim (_, 1) = []
shrinkBranchesSameDim (xs, n) =
  [(IntMap.delete x xs, n - 1) | x <- IntMap.keys xs]
    <> [(IntMap.insert x rx' xs, n) | (x, rx) <- IntMap.assocs xs, rx' <- shrinkNodeSameDim rx]

shrinkRelSameDim :: Relation -> [Relation]
shrinkRelSameDim (xs, w, n) = branchShrinks <> wildShrinks
  where
    branchShrinks = do
      ys <- shrinkBranchesSameDim xs
      let newR = (ys, w, n)
      guard (not $ isEmptyRelation newR)
      pure newR
    wildShrinks = do
      v <- shrinkWild w
      let newR = (xs, v, n)
      guard (not $ isEmptyRelation newR)
      pure newR

shrinkNodeSameDim :: Node -> [Node]
shrinkNodeSameDim End = []
shrinkNodeSameDim (N r) = [N r' | r' <- shrinkRelSameDim r, not (isEmptyRelation r')]

shrinkRelDecreaseDim :: Relation -> [Relation]
shrinkRelDecreaseDim (_, _, n) | n <= 1 = []
shrinkRelDecreaseDim (xs, Nothing, n) | isEmptyBranches xs = [(xs, Nothing, n - 1)]
shrinkRelDecreaseDim (xs, w, _) = [x | N x <- (wildNodes <> branchesNodes)]
  where
    (as, _) = xs
    branchesNodes = IntMap.elems as
    wildNodes = case w of
      Nothing -> []
      Just x -> [x]

---------------------------------------------------
-- Functions for tests
---------------------------------------------------
hasEmpty :: Relation -> Bool
hasEmpty r
  | isEmptyRelation r = True
hasEmpty ((xs, _), w, _) = case w of
  Nothing -> IntMap.null xs || any nodeHasEmpty xs
  Just v -> any nodeHasEmpty xs || nodeHasEmpty v
  where
    nodeHasEmpty End = False
    nodeHasEmpty (N r) | isEmptyRelation r = True | otherwise = hasEmpty r

emptyRelN :: Int -> Relation
emptyRelN n = (empty, empty, n)
