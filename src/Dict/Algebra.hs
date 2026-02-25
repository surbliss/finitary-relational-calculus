{-# LANGUAGE ExtendedDefaultRules #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Dict.Algebra where

import Control.Exception (assert)
import Data.IntMap (IntMap)
import Data.IntMap qualified as Map
import Data.IntSet (IntSet)
import Data.IntSet qualified as Set
import Data.List (intercalate, nub, sort)
import PrettyShow
import Test.QuickCheck hiding ((><))

default (Int)

-- import GHC.TypeLits

-- type Map = IntMap
type Key = Int
type Set = IntSet

--- We reserve '0' as the wild-card, for keys.
type Map = IntMap

-- newtype Map a = Map (Map a) deriving (Show, Eq, Ord, Functor)
-- data Dict a = Map (Dict (Map a))| (:%)

data FWild a = Empty | W a deriving (Show, Eq, Ord, Functor) -- Could just as well use maybe here...

instance PrettyShow Wild where
  pshow Empty = "Ø"
  pshow (W a) = "* -> " ++ pshow a
type RelMap = Map Relation
type Wild = FWild Relation

--- Invariant: _No_ maps into empty dictionaries!
data Relation = R (RelMap, Wild) | Univ deriving (Show, Eq, Ord)
instance PrettyShow Relation where
  pshow Univ = "U"
  pshow (R (xs, Empty)) | Map.null xs = "Ø"
  pshow (R (xs, w)) = "{" ++ elmArrs ++ ", " ++ pshow w ++ "}"
    where
      kvs = Map.assocs xs
      elmArrs = intercalate ", " $ map (\(x, y) -> pshow x ++ " -> " ++ pshow y) kvs
      wArr = case w of
        Empty -> ""
        W w' | isEmpty w' -> ""
        w' -> ", " ++ pshow w'

-- Tmp repl stuff
uuu :: Relation
uuu = finite [1, 2, 3]
vvv :: Relation
vvv = cofinite [2, 3, 4]

--- For retrieving
data Val = V Key | S deriving (Eq, Ord)
instance Show Val where
  show (V k) = show k
  show S = "*"

type Trie = [Val]

class ToSet a where
  toSet :: a -> Set

instance ToSet Set where
  toSet = id

instance ToSet [Int] where
  toSet = Set.fromList

instance ToSet [Integer] where
  toSet = Set.fromList . map fromIntegral

instance ToSet Int where
  toSet = Set.singleton

instance ToSet Integer where
  toSet = Set.singleton . fromIntegral

---------------------------------------------------
-- Exported functionality, reletional funcs
---------------------------------------------------
compl :: Relation -> Relation
compl Univ = empty
compl (R (xs, Empty)) = assert (Map.null xs) $ Univ
compl (R (xs, W ys)) = R (xs, W (compl ys))

-- where
--   ys' = compl ys
--   w' = if ys' == empty then Empty else W ys'

normalize :: Relation -> Relation
normalize Univ = Univ
normalize (R (xs, w)) = R (normalizeMap, normalizeWild w)
  where
    normalizeMap = Map.filter (not . isEmpty) (Map.map normalize xs)

normalizeWild :: Wild -> Wild
normalizeWild (W xs) = case normalize xs of
  xs' | isEmpty xs' -> Empty
  -- xs' | isUniv xs' -> Univ
  xs' -> W xs'
normalizeWild u = u

--- Need to be same dim!
(/\) :: Relation -> Relation -> Relation
Univ /\ x = x
x /\ Univ = x
(R (xs, v)) /\ (R (ys, w)) = R (Map.intersectionWith (/\) xs ys, v `intersectWild` w)

intersectWild :: Wild -> Wild -> Wild
x `intersectWild` Empty = x
Empty `intersectWild` x = x
W v `intersectWild` W w = W (v /\ w)

--- Also needs to be same dim!
(\/) :: Relation -> Relation -> Relation
Univ \/ _ = Univ
_ \/ Univ = Univ
(R (xs, _)) \/ R (ys, Empty) = assert (Map.null xs || Map.null ys) $ empty
(R (xs, Empty)) \/ R (ys, _) = assert (Map.null xs || Map.null ys) $ empty
x@(R (_, W _)) \/ y@(R (_, W _)) = compl $ compl x \\ y

-- (R (xs, v)) \/ (R (ys, w)) = R (Map.unionWith (\/) xs ys, v `unionWild` w)

(\\) :: Relation -> Relation -> Relation
Univ \\ x = compl x
_ \\ Univ = empty
R (xs, v) \\ R (ys, w) = R (Map.differenceWith diff xs ys, wildDiff)
  where
    diff x y = Just (x \\ y)
    wildDiff = case (v, w) of
      (Empty, _) -> Empty
      (x, Empty) -> x
      (W x, W y) -> W $ x \\ y

unionWild :: Wild -> Wild -> Wild
x `unionWild` Empty = x
Empty `unionWild` x = x
W v `unionWild` W w = W (v \/ w)

(><) :: Relation -> Relation -> Relation
Univ >< x = x
x >< Univ = x
(R (xs, w)) >< y = R (Map.map (>< y) xs, wildProd w)
  where
    wildProd Empty = toEmpty y
    wildProd (W v) = W (v >< y)
    toEmpty z = case z of
      Univ -> Empty
      R (_, Empty) -> W empty
      R (_, W v) -> W (R (Map.empty, toEmpty v))

univ :: Relation
univ = Univ

empty :: Relation
empty = R (Map.empty, Empty)

isEmpty :: Relation -> Bool
isEmpty (R (xs, Empty)) = Map.null xs
isEmpty _ = False

--- Note: While Empty always propagates, Univ can be layers deep!
isUniv :: Relation -> Bool
isUniv Univ = True
isUniv (R (xs, W w)) = Map.null xs || isUniv w
isUniv (R (_, Empty)) = False

--- Exported for tests
dictEq :: Relation -> Relation -> Bool
dictEq x y = us == vs
  where
    vs = sort $ nub $ tries x
    us = sort $ nub $ tries y

---------------------------------------------------
-- Interface for interacting with Dicts
---------------------------------------------------
-- normalize :: Relation -> Relation
-- normalize Empty = Empty
-- normalize (R (xs, Univ)) = R (Map.map normalize xs, Univ)
-- normalize (R (xs, W ys)) = case (Map.map normalize xs, normalize ys) of
--   (xs', Univ) -> undefined

--- Constructors
-- empty :: Dict
-- empty = Dict Nothing Map.empty

--- NOTE: Should univ be End or * mapsto End ?
--- Take the one that satisfies compl . compl = id!
-- univ :: Dict
-- univ = End

-- singleton :: Key -> Dict -> Dict
-- singleton k r = Dict Nothing $ Map.singleton k r

finite :: (ToSet a) => a -> Relation
finite x = R (Map.fromSet (\_ -> univ) (toSet x), W empty)

cofinite :: (ToSet a) => a -> Relation
cofinite x = R (Map.fromSet (\_ -> univ) (toSet x), W Univ)

-- cofinite :: (ToSet a) => a -> Dict
-- cofinite x = Dict (Just univ) $ Map.fromSet (const End) set
--   where
--     set = Set.insert 0 (toSet x)

-- --- Retrieving info
-- get :: Key -> Dict -> Maybe Dict
-- get i (Dict _ x) = Map.lookup i x
-- get _ End = Nothing

-- update :: (Dict -> Dict) -> Key -> Dict -> Dict
-- update _ _ End = End
-- update f k (Dict w x) = Dict w $ Map.update mf k x
--   where
--     mf y | isEmpty (f y) = Nothing
--     mf y = Just $ f y

-- updateAll :: (Dict -> Dict) -> Dict -> Dict
-- updateAll _ End = End
-- updateAll f (Dict w x) = Dict w $ Map.mapWithKey (update f) x

-- updateWild :: (Dict -> Dict) -> Key -> Dict -> Dict
-- updateWild _ _ End = End
-- updateWild f k (Dict w x) = Dict w' x
--   where
--     w' = if maybe True isEmpty (update f k <$> w) then Nothing else w'

-- elemsMap :: (Dict -> Dict) -> Dict -> Dict
-- elemsMap _ End = End
-- elemsMap f (Dict w x) = Dict w $ Map.map f x

-- apply :: (Dict -> Dict) -> Dict -> Dict
-- apply _ End = End
-- apply f (Dict w d) = case f d of {}

-- applyWild :: (Dict -> Dict) -> Dict -> Dict
-- applyWild _ End = End
-- applyWild _ (Dict Nothing x) = Dict Nothing x
-- applyWild f (Dict (Just x) y) =
--   let res = f x
--    in if isEmpty res then Dict Nothing y else Dict (Just res) x

-- getWild :: Dict -> Wild Dict
-- getWild (Dict w _) = w
-- getWild End = Nothing

-- setWild :: Wild Dict -> Dict -> Dict
-- setWild w (Dict _ x) = Dict w x
-- setWild Nothing End = End
-- setWild (Just x) End = Dict (Just x) Map.empty

-- fromList :: Wild Dict -> [(Key, Dict)] -> Dict
-- fromList w xs = Dict w $ Map.fromList xs

-- insert :: Key -> Dict -> Dict -> Dict
-- insert k v (Dict w x) = Dict w $ (Map.insert k v) x
-- insert k v End = singleton k v

-- {x -> [], * -> []}
-- delete :: Key -> Dict -> Dict
-- delete k (Dict w r) = Dict w $ Map.delete k r
-- delete _ End = End

-- finKeys :: Dict -> Set
-- finKeys (Dict _ x) = Map.keysSet x
-- finKeys End = Set.empty

-- vals :: Dict -> [Val]
-- vals (Dict (Just _) r) = S : map V (Map.keys r)
-- vals (Dict Nothing r) = map V (Map.keys r)
-- vals (End) = [S]

----------------------------------------------------
-- Query-specific stuff
---------------------------------------------------
-- contains :: [Key] -> Relation -> Bool
-- contains [] _ = True
-- contains (x : xs) y = case (get x y, wild y) of
--   (Nothing, Nothing) -> False
--   (Nothing, Just z) -> contains xs z
--   (Just z, Nothing) -> contains xs z
--   (Just z, Just w) -> contains xs z /= contains xs w

-- isEmpty :: Dict -> Bool
-- isEmpty (Dict Nothing x) = Map.null x
-- isEmpty (Dict (Just _) _) = False
-- isEmpty End = False

-- isUniv :: Dict -> Bool
-- isUniv (Dict Nothing _) = False
-- isUniv (Dict (Just x) y) = isUniv x && Map.null y
-- isUniv End = True

-- (><) :: Dict -> Dict -> Dict
-- x >< End = x
-- End >< y = y
-- x >< y | isEmpty x || isEmpty y = empty
-- x >< y = elemsMap (>< y) x

-- compl :: Dict -> Dict
-- compl End = empty
-- compl (Dict Nothing x) | Map.null x = End
-- compl (Dict Nothing x) = Dict (Just univ) x
-- compl (Dict (Just x) y) = Dict (Just (compl x)) y

-- (/\) :: Dict -> Dict -> Dict
-- End /\ y = y
-- x /\ End = x
-- Dict _ x /\ Dict _ y = Dict Nothing $ Map.intersectionWith (/\) x y

-- --- This is the hard one... Don't think this is correct. But good enough for tests!
-- (\/) :: Dict -> Dict -> Dict
-- End \/ y = y
-- x \/ End = x
-- Dict _ x \/ Dict _ y = Dict Nothing $ Map.unionWith (\/) x y

-- ---------------------------------------------------
-- -- Testing help
-- ---------------------------------------------------
tries :: Relation -> [Trie]
tries (Univ) = [[S]]
tries (R (xs, w)) = fins ++ wilds
  where
    fins = do
      (k, v) <- Map.assocs xs
      (V k :) <$> tries v
    wilds = case w of
      Empty -> []
      W x -> (S :) <$> tries x

-- valLt :: Val -> Val -> Bool
-- S `valLt` S = True
-- V _ `valLt` S = True
-- S `valLt` V _ = False
-- V x `valLt` V y = x == y

-- trieLt :: Trie -> Trie -> Bool
-- trieLt [] _ = True
-- trieLt (S : xs) [] = trieLt xs []
-- trieLt (V _ : _) [] = False
-- trieLt (x : xs) (y : ys) = valLt x y && trieLt xs ys

-- containsTrie :: Dict -> Trie -> Bool
-- containsTrie _ [] = True
-- containsTrie End _ = True
-- containsTrie (Dict Nothing _) (S : _) = False
-- containsTrie (Dict (Just w) _) (S : xs) = containsTrie w xs
-- containsTrie y (V x : xs) = case (get x y, wild y) of
--   (Nothing, Nothing) -> False
--   (Nothing, Just z) -> containsTrie z xs
--   (Just z, Nothing) -> containsTrie z xs
--   (Just z, Just w) -> containsTrie z xs /= containsTrie w xs

---------------------------------------------------
-- For assert-repl-testing
---------------------------------------------------
-- noNulls :: Dict -> Bool
-- noNulls End = True
-- noNulls (Dict _ x) | Map.null x = False
-- noNulls (Dict x y) = all noNulls y || maybe True noNulls x

-- valid :: Dict -> Bool
-- valid x = isEmpty x || noNulls x

-- uuu :: Dict
-- uuu = finite 1

-- vvv :: Dict
-- vvv = cofinite 2

-- pshow :: Dict -> String
-- pshow = undefined
---------------------------------------------------
-- TRY 2: Helper-functions
---------------------------------------------------
lookupKey :: Key -> Relation -> Maybe Relation
lookupKey _ Univ = Nothing
lookupKey k (R (xs, _)) = Map.lookup k xs

lookupWild :: Relation -> Maybe Relation
lookupWild Univ = Nothing
lookupWild (R (_, Empty)) = Nothing
lookupWild (R (_, W w)) = Just w

depth :: Relation -> Int
depth Univ = 0
depth (R (xs, w)) = case (Map.elems xs, w) of
  ([], Empty) -> 0
  ([], W w') -> 1 + depth w'
  (y : _, _) -> 1 + depth y

depthsAll :: Relation -> [Int]
depthsAll Univ = [0]
depthsAll (R (xs, Empty)) = do
  v <- Map.elems xs
  d <- depthsAll v
  pure $ 1 + d
depthsAll (R (xs, W w)) = depthsAll (R (xs, Empty)) <> ((1 +) <$> depthsAll w)

---------------------------------------------------
-- Generator + arbitrary
arbitraryRelMap :: Gen RelMap
arbitraryRelMap = do
  n <- chooseInt (0, 5)
  genRelMap n

--- Don't shrink into empties!
shrinkRelMap :: RelMap -> [RelMap]
shrinkRelMap xs = deletedKeys ++ shrunkElems
  where
    deletedKeys = [Map.delete x xs | x <- Map.keys xs] -- NOTE: Can also product empty mapping
    shrunkElems =
      [ Map.insert x ys' xs
      | (x, ys) <- Map.assocs xs
      , ys' <- shrink ys
      -- , not (isEmpty ys') -- _But_ never allow binding a key to an empty map!
      ]

instance Arbitrary Relation where
  arbitrary = do
    n <- chooseInt (0, 5)
    genRel n

  -- shrink Empty = []
  shrink Univ = [empty]
  --- Here xs should have depth 1?
  shrink (R (xs, Empty)) = [R (xs', Empty) | xs' <- shrinkRelMap xs]
  shrink (R (xs, W ys)) =
    [R (xs', W ys) | xs' <- shrinkRelMap xs]
      ++ [R (xs, W ys') | ys' <- shrink ys]
      ++ [R (xs, Empty)]
      ++ [projLast (R (xs, W ys))]

projLast :: Relation -> Relation
projLast Univ = Univ
projLast (R (_, Empty)) = empty
projLast (R (_, W Univ)) = Univ
projLast (R (_, W (R (_, Empty)))) = Univ
projLast (R (xs, W w)) = R (Map.map projLast xs, W (projLast w))

genRel :: Int -> Gen Relation
genRel n | n < 1 = pure univ
genRel n = do
  nKeys <- chooseInt (1, 5)
  keys <- vectorOf nKeys (arbitrary :: Gen Key)
  ds <- vectorOf nKeys $ genRel (n - 1)
  w <- genWild (n - 1)
  pure $ R (Map.fromList (zip keys ds), w)

genWild :: Int -> Gen Wild
genWild n | n < 0 = pure Empty
genWild n = W <$> genRel n

genRelMap :: Int -> Gen RelMap
genRelMap n | n < 1 = pure Map.empty
genRelMap n = do
  nKeys <- chooseInt (1, 5)
  keys <- vectorOf nKeys arbitrary
  vals <- vectorOf nKeys (frequency [(2, genRel (n - 1)), (1, pure univ)])
  pure $ Map.fromList (zip keys vals)
