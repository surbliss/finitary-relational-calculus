{-# LANGUAGE ExtendedDefaultRules #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Dict.Algebra where

import Control.Exception (assert)
import Data.IntMap.Strict qualified as IntMap
import PrettyShow
import Test.QuickCheck hiding ((><))
import Text.Show qualified
import Prelude hiding (Alternative (empty), nonEmpty)

type Wild = Maybe Node
type Branches = (IntMap Node, Int) -- Map with its size
data Node = Empty | N Relation | End deriving (Show, Eq, Ord)
type Relation = (Branches, Wild, Int) -- Relation with its depth
-- data Relation
--   = R
--   { depth :: Int -- To avoid traversing, when converting to Nothing
--   -- , count :: Int -- number of keys
--   , wild :: Wild
--   , branches :: Branches
--   }
--   deriving (Show, Eq, Ord)
---------------------------------------------------
-- Dictionary-helpers
---------------------------------------------------

dim :: Relation -> Int
dim (_, _, n) = n

count :: Branches -> Int
count (_, i) = i

bmap :: (Node -> Node) -> Branches -> Branches
bmap f (xs, n) = (IntMap.map f xs, n)
  where

-- Just computes the size, and adds that
branches :: IntMap Node -> Branches
branches xs = (xs, IntMap.size xs)

-- First branchs: The lookup-branch. Defer evaluation of f, till we see if the
-- given key is even present in second branchs
-- interWith :: (Node -> Node) -> Branches -> Branches -> Branches
-- interWith f (xs, _) (ys, _) = (res, IntMap.size res)
--   where
--     res = IntMap.mapMaybeWithKey combine xs
--     combine x rx = case (IntMap.lookup x ys) of
--       Nothing -> Nothing
--       Just ry -> nonEmpty (rx /\ f ry)

---------------------------------------------------
-- Transformer-classes for normalizing
---------------------------------------------------
class Algebra a where
  -- Intersection, Symmetric difference, Union, Difference
  (/\), (\/), (<+>), (\\) :: a -> a -> a

  -- Identity for <+> and \/, annihilator for /\
  empty :: a

class (Algebra a) => Negatable a where
  neg :: a -> a -- Complement
  univ :: a -- = neg empty

-- Cartesian product
class Extendable a where
  (><) :: a -> Relation -> a

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
  Just w \/ Just v = Just (w \/ v)

  Nothing \\ _ = empty
  x \\ Nothing = x
  Just x \\ Just y = nonEmpty $ x \\ y

  Nothing <+> y = y
  y <+> Nothing = y
  Just x <+> Just y = nonEmpty $ x <+> y

  empty = Nothing

-- Note: Wild _can't_ be negated, because we don't know how deep 'Empty' is outside of a relation!

-- Q: Should we assert only End with End here?
node :: Relation -> Node
node r
  | isEmptyRelation r = Empty
  | otherwise = N r
instance Algebra Node where
  End /\ End = End
  Empty /\ _ = Empty
  _ /\ Empty = Empty
  End /\ _ = error "/\\Right node deeper"
  _ /\ End = error "/\\ Left node deeper"
  N r /\ N s = node (r /\ s)

  End \/ End = End
  Empty \/ x = x
  x \/ Empty = x
  End \/ _ = error "\\/ Right node deeper"
  _ \/ End = error "\\/ Left node deeper"
  N r \/ N s = N (r \/ s)

  End \\ End = Empty
  Empty \\ _ = Empty
  x \\ Empty = x
  End \\ _ = error "\\\\ Right node deeper"
  _ \\ End = error "\\\\ Left node deeper"
  N x \\ N y = node (x \\ y)

  End <+> End = Empty
  Empty <+> x = x
  x <+> Empty = x
  End <+> _ = error "<+> Right node deeper"
  _ <+> End = error "<+> Left node deeper"
  N x <+> N y = node (x <+> y)

  empty = Empty

instance Negatable Node where
  univ = End

  neg End = empty
  neg Empty = univ
  neg (N r) = node (neg r)

--- Some helper-functions for Algebra Relation instance below:
updateBranch :: (Node -> Node) -> Branches -> Branches
updateBranch f (xs, _) = (res, IntMap.size res)
  where
    res = IntMap.mapMaybe (nonEmpty . f) xs

-- Lookup x into first branch, and compute x /\ (y + w) if  present
interSym :: Branches -> Branches -> Node -> Branches
interSym (xs, _) (ys, _) wy = branches $ IntMap.mapMaybeWithKey comb xs
  where
    comb x ra = case (IntMap.lookup x ys) of
      Nothing -> nonEmpty (ra /\ wy)
      Just rx -> nonEmpty $ ra /\ (rx <+> wy)

-- Lookup x into first branch, and compute x /\ y if  present
inter :: Branches -> Node -> Branches
inter (xs, _) y = branches $ IntMap.mapMaybe (\x -> nonEmpty (x /\ y)) xs

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

instance Negatable Relation where
  neg (_, _, 0) = error "Can't negate 0-dim"
  neg (xs, Nothing, n) = (xs, Just ((univN (n - 1))), n)
  neg (xs, Just w, n) = (xs, nonEmpty (neg w), n)

  -- Univ relation is {* -> E}
  univ = (empty, Just univ, 1)

--- For all these: Only do the 'isEmptyRelation' check in the actual relation definition
instance Extendable Branches where
  (xs, n) >< r = (xs <&> (>< r), n)

-- instance Extendable Wild where
--   w >< r = w <&> (>< r)

instance Extendable Node where
  End >< r = N r
  Empty >< _ = empty
  N s >< r = N (s >< r)

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

{- | Simplifies the data-structures, by removing maps to empty relations
Note that these only ever checks _one_ level down, so they are save to use
inside recursive definitions.
-}
isEmptyBranches :: Branches -> Bool
isEmptyBranches (xs, n) | n == 0 = assert (IntMap.null xs) True
isEmptyBranches _ = False

isEmptyRelation :: Relation -> Bool
isEmptyRelation (xs, Nothing, _) = isEmptyBranches xs
isEmptyRelation _ = False

nonEmpty :: Node -> Maybe Node
nonEmpty Empty = Nothing
nonEmpty x = Just x

-- nonEmptyWild :: Node -> Wild
-- nonEmptyWild End = Just End
-- nonEmptyWild (N r) = nonEmpty r

-- removeEmptyBranches :: Branches -> Branches
-- removeEmptyBranches (xs, _) = (IntMap.filter (not . isEmptyNode))
removeEmpty :: IntMap Node -> Branches
removeEmpty xs = branches $ IntMap.filter (/= Empty) xs

-- simplifyWild :: Wild -> Wild
-- simplifyWild Nothing = Nothing
-- -- simplifyWild Univ = Univ
-- simplifyWild (Just w)
--   | isEmptyRelation w = Nothing
--   | otherwise = Just w

-- simplify :: Relation -> Relation
-- simplify r = r {branches = removeEmptyBranches (branches r), wild = simplifyWild (wild r)}

-- isUnivRelation :: Relation -> Bool
-- -- isUnivRelation R {branches = xs, wild = Univ} = assert (IntMap.null xs) True
-- isUnivRelation R {wild = Nothing} = False
-- isUnivRelation R {branches = xs, wild = Just w} = IntMap.null xs && isUnivRelation w

{- | Update the count of branches - use after op that might modify these
getCount :: Branches -> Int
getCount bs = IntMap.size bs
-}

-- updateCount :: Relation -> Relation
-- updateCount r = r {count = getCount (branches r)}

-- WRONG: Attempty at projection, but _wrong_: Projection over symmetric difference is
-- more complicated than this
-- projLast :: Relation -> Relation
-- projLast R {depth = 0} = empty
-- N projLast r@R {depth = 1}
--   | isEmptyRelation r = empty
--   | otherwise = univ
-- N projLast r@R {branches = xs, depth = n} =
--   r
--     { branches = projLast <$> xs
--     , wild = newWild
--     , depth = n - 1
--     }
--   where
--     newWild = case wild r of
--       Nothing -> Nothing
--       -- Univ -> Univ
--       Just w -> Just (projLast w)

univN :: Int -> Node
univN n | n < 0 = error "Negative dimension for univN"
univN 0 = End
univN n = N (empty, Just (univN (n - 1)), n)

---------------------------------------------------
-- Printing and checking
---------------------------------------------------

--- For retrieving
data Val = V Int | S deriving (Eq, Ord)
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
finite :: (ToIntSet a) => a -> Relation
finite x = (branches bs, empty, 1)
  where
    bs = IntMap.fromSet (\_ -> univ) (toSet x)

cofinite :: (ToIntSet a) => a -> Relation
cofinite x = (branches bs, Just univ, 1)
  where
    bs = IntMap.fromSet (\_ -> univ) (toSet x)

--- Finite pairs
pairs :: [(Int, Int)] -> Relation
pairs xs = (branches bs, empty, 2)
  where
    mkRelation (x, y) = (x, N (finite y))
    bs = IntMap.fromListWith (\/) $ map mkRelation xs

triples :: [(Int, Int, Int)] -> Relation
triples xs = foldr (\/) (empty >< empty >< empty) [finite [x] >< (finite [y]) >< (finite [z]) | (x, y, z) <- xs]

---------------------------------------------------
-- Pretty-printing
---------------------------------------------------
-- showDetails :: Relation -> String
-- showDetails r = "|" <> "c" <> show (count r) <> "," <> "d" <> show (depth r) <> "|"

-- Same here
isUniv :: Relation -> Bool
-- isUniv R {branches = xs, wild = Univ, depth = n} =
-- assert
--   (n == 0 && IntMap.null xs)
--   True
isUniv _ = False
instance PrettyShow Node where
  pshow End = "E"
  pshow Empty = "Ø"
  pshow (N r) = pshow r

instance PrettyShow Relation where
  pshow (bs, Nothing, n) = "{#" ++ show n ++ ":" ++ pshow bs ++ "}"
  pshow (bs, w, n) = "{#" ++ show n ++ ":" ++ pshow bs ++ ", " ++ pshow w ++ "}"

instance PrettyShow Branches where
  pshow (xs, n) =
    assert (IntMap.size xs == n) xs
      & IntMap.toAscList
      & map pshowBranch
      & intercalate ", "
    where
      pshowBranch (x, rx) = show x ++ "->" ++ pshow rx

-- pshow r
--   | isUniv r = "U"
--   | isEmptyRelation r = show (depth r) <> "Ø"
--   | otherwise = "{" <> intercalate ", " pretties <> "}"
--   where
--     pretties = prettyBranches (branches r) <> prettyWild (wild r)
--     prettyBranches xs = xs & IntMap.toList <&> prettyMap
--     prettyMap (k, v) = pshow k <> " -> " <> pshow v
--     prettyWild Nothing = []
--     -- prettyWild Univ = ["* -> U"]
--     prettyWild (Just w) = ["* -> " <> pshow w]

instance PrettyShow Wild where
  pshow w = case w of
    Nothing -> ""
    Just a -> "* -> " <> pshow a

---------------------------------------------------
-- Generator
---------------------------------------------------
--- Newtype wrappers to enforce consistent dims for pairs and triples of relations
newtype Relation1 = Rel1 (Relation) deriving (Show, Eq, Ord)
newtype Relation2 = Rel2 (Relation, Relation) deriving (Show, Eq, Ord)
newtype Relation3 = Rel3 (Relation, Relation, Relation) deriving (Show, Eq, Ord)

getLayers :: Gen Int
getLayers = do
  size <- getSize
  chooseInt (1, max 1 $ size)

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
-- shrinkWild Univ = [Nothing]
shrinkWild (Just w) = [nonEmpty w' | w' <- shrinkNodeSameDim w]

shrinkWildDecreaseDim :: Wild -> [Wild]
shrinkWildDecreaseDim Nothing = []
-- shrinkWildDecreaseDim Univ = [Univ]
shrinkWildDecreaseDim (Just w) = [nonEmpty w' | w' <- shrinkNodeDecreaseDim w]

-- shrinkWild (Just w) = [Just w' | w' <- shrink w, not (isEmptyRelation w)]

shrinkBranchesSameDim :: Branches -> [Branches]
shrinkBranchesSameDim (_, 0) = []
shrinkBranchesSameDim (_, 1) = []
shrinkBranchesSameDim (xs, n) =
  [(IntMap.delete x xs, n - 1) | x <- IntMap.keys xs]
    <> [(IntMap.insert x rx' xs, n) | (x, rx) <- IntMap.assocs xs, rx' <- shrinkNodeSameDim rx]

-- shrinkKeys = [B (IntMap.insert x (removeEmpty v') xs) | (x, v) <- IntMap.assocs xs, v' <- shrinkRelSameDim v]

-- shrinkVal = [B $ IntMap.insert k v' xs | (k, v) <- IntMap.assocs xs, v' <- shrink v, not (isEmptyRelation v')]

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
shrinkNodeSameDim Empty = []
shrinkNodeSameDim (N r) = [N r' | r' <- shrinkRelSameDim r, not (isEmptyRelation r')]

shrinkNodeDecreaseDim :: Node -> [Node]
shrinkNodeDecreaseDim End = []
shrinkNodeDecreaseDim Empty = []
shrinkNodeDecreaseDim (N r) = [N x | x <- shrinkRelDecreaseDim r]

shrinkRelDecreaseDim :: Relation -> [Relation]
shrinkRelDecreaseDim (_, _, n) | n <= 1 = []
shrinkRelDecreaseDim (xs, Nothing, n) | isEmptyBranches xs = [(xs, Nothing, n - 1)]
shrinkRelDecreaseDim (xs, w, _) = [x | N x <- (wildNodes <> branchesNodes)]
  where
    (as, _) = xs
    branchesNodes = IntMap.elems as
    wildNodes = case w of
      Nothing -> []
      -- Univ -> pure $ univN (depth r - 1)
      Just x -> [x]

---------------------------------------------------
-- Functions for tests
---------------------------------------------------
hasEmpty :: Relation -> Bool
hasEmpty r
  | isEmptyRelation r = True
  | isUniv r = False
hasEmpty ((xs, _), w, _) = case w of
  -- Univ -> any hasEmpty xs
  Nothing -> IntMap.null xs || any nodeHasEmpty xs
  Just v -> any nodeHasEmpty xs || nodeHasEmpty v
  where
    nodeHasEmpty End = False
    nodeHasEmpty Empty = True
    nodeHasEmpty (N r) = hasEmpty r

-- tries :: (Relation) -> [Trie]
-- -- tries R {branches = xs, wild = Univ} | IntMap.null xs = [[S]]
-- tries ((xs, _), w, _) = fins ++ wilds
--   where
--     fins = do
--       (k, v) <- IntMap.assocs xs
--       (V k :) <$> tries v
--     wilds = case w of
--       Nothing -> []
--       -- Univ -> [[S]]
--       Just x -> (S :) <$> tries x

-- eq :: Relation -> Relation -> Bool
-- r `eq` s = sortNub (tries r) == sortNub (tries s)

depth :: Relation -> Int
depth (_, _, n) = n

emptyRelN :: Int -> Relation
emptyRelN n = (empty, empty, n)

univRelN :: Int -> Relation
univRelN n = (empty, Just (univN (n - 1)), n)
