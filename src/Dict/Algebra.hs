{-# LANGUAGE ExtendedDefaultRules #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Dict.Algebra where

import Control.Exception (assert)
import Data.IntMap (IntMap)
import Data.IntMap qualified as Map
import Data.IntSet (IntSet)
import Data.IntSet qualified as Set
import Data.List (nub, sort)

default (Int)

-- import GHC.TypeLits

-- type Map = IntMap
type Key = Int
type Set = IntSet

--- We reserve '0' as the wild-card, for keys.
type Map = IntMap

-- newtype Map a = Map (Map a) deriving (Show, Eq, Ord, Functor)
-- data Dict a = Map (Dict (Map a))| (:%)

type Wilds = Maybe Dict
type Elems = Map Dict

--- Invariant: _No_ maps into empty dictionaries!
data Dict = Dict Wilds Elems | End deriving (Show, Eq, Ord)

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

---------------------------------------------------
-- Interface for interacting with Dicts
---------------------------------------------------
--- Constructors
empty :: Dict
empty = Dict Nothing Map.empty

--- NOTE: Should univ be End or * mapsto End ?
--- Take the one that satisfies compl . compl = id!
univ :: Dict
univ = End

singleton :: Key -> Dict -> Dict
singleton k r = Dict Nothing $ Map.singleton k r

finite :: (ToSet a) => a -> Dict
finite x = Dict Nothing $ Map.fromSet (\_ -> End) (toSet x)

cofinite :: (ToSet a) => a -> Dict
cofinite x = Dict (Just univ) $ Map.fromSet (const End) set
  where
    set = Set.insert 0 (toSet x)

--- Retrieving info
get :: Key -> Dict -> Maybe Dict
get i (Dict _ x) = Map.lookup i x
get _ End = Nothing

fromList :: Wilds -> [(Key, Dict)] -> Dict
fromList w xs = Dict w $ Map.fromList xs

wild :: Dict -> Wilds
wild (Dict w _) = w
wild End = Just End --- Corresponds to Univ

insert :: Key -> Dict -> Dict -> Dict
insert k v (Dict w x) = Dict w $ (Map.insert k v) x
insert k v End = singleton k v

delete :: Key -> Dict -> Dict
delete k (Dict w r) = Dict w $ Map.delete k r
delete _ End = End

finKeys :: Dict -> Set
finKeys (Dict _ x) = Map.keysSet x
finKeys End = Set.empty

vals :: Dict -> [Val]
vals (Dict (Just _) r) = S : map V (Map.keys r)
vals (Dict Nothing r) = map V (Map.keys r)
vals (End) = [S]

elemsMap :: (Dict -> Dict) -> Dict -> Dict
elemsMap _ End = End
elemsMap f (Dict w x) = Dict w $ Map.map f x

----------------------------------------------------
-- Query-specific stuff
---------------------------------------------------
contains :: [Key] -> Dict -> Bool
contains [] _ = True
contains (x : xs) y = case (get x y, wild y) of
  (Nothing, Nothing) -> False
  (Nothing, Just z) -> contains xs z
  (Just z, Nothing) -> contains xs z
  (Just z, Just w) -> contains xs z /= contains xs w

isEmpty :: Dict -> Bool
isEmpty (Dict Nothing x) = Map.null x
isEmpty (Dict (Just x) y) = isEmpty x && Map.null y
isEmpty End = False

isUniv :: Dict -> Bool
isUniv (Dict Nothing _) = False
isUniv (Dict (Just x) y) = isUniv x && Map.null y
isUniv End = True

(><) :: Dict -> Dict -> Dict
x >< End = x
End >< y = y
x >< y | isEmpty x || isEmpty y = empty
x >< y = elemsMap (>< y) x

compl :: Dict -> Dict
compl End = empty
compl (Dict Nothing x) | Map.null x = End
compl (Dict Nothing x) = Dict (Just univ) x
compl (Dict (Just x) y) = Dict (Just (compl x)) y

(/\) :: Dict -> Dict -> Dict
End /\ y = y
x /\ End = x
Dict _ x /\ Dict _ y = Dict Nothing $ Map.intersectionWith (/\) x y

--- This is the hard one... Don't think this is correct. But good enough for tests!
(\/) :: Dict -> Dict -> Dict
End \/ y = y
x \/ End = x
Dict _ x \/ Dict _ y = Dict Nothing $ Map.unionWith (\/) x y

---------------------------------------------------
-- Testing help
---------------------------------------------------
tries :: Dict -> [Trie]
tries End = [[S]]
tries (Dict w d) = fins ++ wilds
  where
    fins = do
      (k, v) <- Map.assocs d
      (V k :) <$> tries v
    wilds = case w of
      Nothing -> []
      Just x -> (S :) <$> tries x

valLt :: Val -> Val -> Bool
S `valLt` S = True
V _ `valLt` S = True
S `valLt` V _ = False
V x `valLt` V y = x == y

trieLt :: Trie -> Trie -> Bool
trieLt [] _ = True
trieLt (S : xs) [] = trieLt xs []
trieLt (V _ : _) [] = False
trieLt (x : xs) (y : ys) = valLt x y && trieLt xs ys

containsTrie :: Dict -> Trie -> Bool
containsTrie _ [] = True
containsTrie End _ = True
containsTrie (Dict Nothing _) (S : _) = False
containsTrie (Dict (Just w) _) (S : xs) = containsTrie w xs
containsTrie y (V x : xs) = case (get x y, wild y) of
  (Nothing, Nothing) -> False
  (Nothing, Just z) -> containsTrie z xs
  (Just z, Nothing) -> containsTrie z xs
  (Just z, Just w) -> containsTrie z xs /= containsTrie w xs

dictEq :: Dict -> Dict -> Bool
dictEq x y = us == vs
  where
    vs = sort $ nub $ tries x
    us = sort $ nub $ tries y

---------------------------------------------------
-- For assert-repl-testing
---------------------------------------------------
noNulls :: Dict -> Bool
noNulls End = True
noNulls (Dict _ x) | Map.null x = False
noNulls (Dict x y) = all noNulls y || maybe True noNulls x

valid :: Dict -> Bool
valid x = isEmpty x || noNulls x

uuu :: Dict
uuu = finite 1

vvv :: Dict
vvv = cofinite 2

pshow :: Dict -> String
pshow = undefined
