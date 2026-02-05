{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE PatternSynonyms #-}

{- | Internal constructors that maintain ordering of algebra terms.
Not to be exported directly, but to be used internally only
-}
module Algebra (
  Finitary (..),
  Intersection (..),
  Product (..),
  Union (..),
  InternalAlgebra (..),
  PrettyShow (..),
  pprint,
  empty,
  univ1,
  perm,
  proj,
  diag,
) where

import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty ((:|)), nonEmpty, toList)
import Data.List.NonEmpty qualified as NE

data Finitary a = Finite a | Cofinite a deriving (Eq, Show, Functor)

newtype Intersection a = Intersection [Finitary a] deriving (Eq, Show, Functor)

newtype Product a = Product (NonEmpty (Intersection a)) deriving (Eq, Show, Functor)
newtype Union a = Union [Product a] deriving (Eq, Show, Functor)

empty :: Union a
empty = Union []

--- 1-dimensional U
univ1 :: Union a
univ1 = single $ Intersection []

--- Internal computations
-- NOT to be exported, helper-functions for internal algebra-calculations
class InternalAlgebra t where
  -- Each type is responsible for one of these, the rest propagates:
  single :: t a -> Union a
  compl' :: t a -> Union a -- Finitary
  (/\) :: t a -> t a -> Union a -- Intersection
  (><) :: t a -> t a -> Union a -- Product
  (\/) :: t a -> t a -> Union a -- Union

instance InternalAlgebra Finitary where
  single x = single $ Intersection [x]

  compl' (Finite x) = single $ Cofinite x
  compl' (Cofinite x) = single $ Finite x

  x /\ y = single x /\ single y
  x >< y = single x >< single y
  x \/ y = single x \/ single y

instance InternalAlgebra Intersection where
  single x = single $ Product $ x :| []

  -- Intersection should handle Univ-rules
  compl' (Intersection []) = empty
  -- (21), i.e. DeMorgan
  compl' (Intersection (x : xs)) = compl' x \/ compl' (Intersection xs)

  -- Note that xs/ys = [] acts asunivUnion here!
  Intersection xs /\ Intersection ys = single $ Intersection $ xs <> ys

  x >< y = single $ Product $ x :| [y]

  Intersection [] \/ _ = univ1
  _ \/ Intersection [] = univ1
  x \/ y = single x \/ single y

instance InternalAlgebra Product where
  single x = Union [x]

  -- (22)
  compl' (Product (x :| [])) = compl' x
  compl' (Product (x :| (y : ys))) =
    (compl' x >< univs)
      \/ (univ1 >< compl' (Product (y :| ys)))
    where
      univs = single $ Product $ NE.map (const $ Intersection []) $ y :| ys

  -- (30)
  Product (x :| xs) /\ Product (y :| ys) = case (nonEmpty xs, nonEmpty ys) of
    (Nothing, Nothing) -> x /\ y
    (Just xs', Just ys') -> (x /\ y) >< (Product xs' /\ Product ys')
    (Nothing, Just _) -> error "Right product longer than left in intersection"
    (Just _, Nothing) -> error "Left product longer than right in intersection"

  Product xs >< Product ys = single $ Product (xs <> ys)

  x \/ y = single x \/ single y

instance InternalAlgebra Union where
  single = id -- Not needed
  -- DeMorgan

  compl' (Union []) = error "TODO: Need a way to determine dimension here..."
  compl' (Union [x]) = compl' x
  compl' (Union (x : xs)) = compl' x /\ compl' (Union xs)

  Union [] /\ _ = empty
  _ /\ Union [] = empty
  -- (28)-(29)
  Union [x] /\ Union ys = foldl (\/) empty xIntersections
    where
      xIntersections = map (x /\) ys
  Union (x : xs) /\ Union ys = (single x /\ Union ys) \/ (Union xs /\ Union ys)

  -- Union [x] /\ Union (y : ys) = (x /\ y) \/ single x /\ Union ys
  -- Union (x : xs) /\ Union (y : ys) =
  --   (x /\ y)
  --     \/ (single x /\ Union ys)
  --     \/ (Union xs /\ single y)
  --     \/ (Union xs /\ Union ys)

  -- (31)-(32) + emptyUnion products
  Union [] >< _ = empty
  _ >< Union [] = empty
  Union (x : xs) >< Union (y : ys) =
    (x >< y)
      \/ (Union [x] >< Union ys)
      \/ (Union xs >< Union [y])
      \/ (Union xs >< Union ys)

  -- Note that xs/ys = [] acts as empty-set, so these lines are technically unecessary
  x \/ Union [] = x
  Union [] \/ x = x
  -- Filter univs away here! I.e. 1 x 1 x 1
  -- WRONG: Should not filter univs, should turn everything _into_ univ!
  Union xs \/ Union ys
    | hasUnivs = univs
    | otherwise = Union $ xs <> ys
    where
      hasUnivs = any isUniv xs || any isUniv ys
      isUniv (Product zs) = all (\(Intersection is) -> null is) zs
      univs = single $ Product $ NE.map (const $ Intersection []) $ ps
      Product ps = xs !! 0

--- Relational algegra-functions
perm :: [Int] -> Union a -> Union a
perm = undefined

--- NOTE: We cut out the _first_ instead of last element, to optimize for
-- Haskell Linked-list implementations
proj :: Union a -> Union a
-- Empty union.
-- NOTE: Maybe proj on Ø should be an error instead? Hm
proj (Union []) = empty
-- First product has dim 1, so all products have dim 1, so projection is empty
proj (Union (Product (_ :| []) : _)) = error ""
-- By invariant that dims of xs are constant, _all_ dims are > 1 here.
proj (Union xs) = foldl (\/) empty (map projProd xs)

projProd :: Product a -> Union a
projProd (Product (_ :| [])) = error "Term-constructor should prevent proj on dim=1"
projProd (Product (_ :| y : ys)) = single $ Product $ y :| ys

diag :: Union a -> Union a
diag (Union []) = Union []
diag (Union xs) = foldl (\/) empty (map diagProd xs)

-- TODO: Normalize, to remove potential 'univs'
diagProd :: Product a -> Union a
diagProd (Product (_ :| [])) = error "Term-constructor should prevent diag on dim=1"
diagProd (Product (Intersection xs :| Intersection ys : zs)) =
  single $ Product (Intersection (xs <> ys) :| zs)

---------------------------------------------------

-- Pretty-printing
---------------------------------------------------
class PrettyShow a where
  pshow :: a -> String

withOp :: (PrettyShow a) => String -> [a] -> String
withOp op xs = intercalate op (map pshow xs)

withParens :: String -> String
withParens s = "(" ++ s ++ ")"

instance PrettyShow String where
  pshow xs = xs

instance PrettyShow Int where
  pshow xs = show xs

instance (PrettyShow a) => PrettyShow (Finitary a) where
  pshow (Finite x) = pshow x
  pshow (Cofinite x) = pshow x ++ "ᶜ"

instance (PrettyShow a) => PrettyShow (Intersection a) where
  pshow (Intersection []) = "𝕌"
  pshow (Intersection [x]) = pshow x
  pshow (Intersection xs) = withOp "∩" xs

instance (PrettyShow a) => PrettyShow (Product a) where
  pshow (Product (x :| [])) = pshow x
  pshow (Product xs) = withParens $ withOp " × " (toList xs)

instance (PrettyShow a) => PrettyShow (Union a) where
  pshow (Union []) = "∅"
  pshow (Union [x]) = pshow x
  pshow (Union xs) = withOp " ∪ " xs

pprint :: (PrettyShow a) => a -> IO ()
pprint = putStrLn . pshow
