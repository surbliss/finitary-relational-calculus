{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE PatternSynonyms #-}

{- | Internal constructors that maintain ordering of algebra terms.
Not to be exported directly, but to be used internally only
-}
module Generic.Algebra (
  Finitary (..),
  Intersection (..),
  Times (..),
  Union (..),
  InternalAlgebra (..),
  PrettyShow (..),
  pprint,
  empty1,
  univ1,
  -- perm,
  proj,
  diag,
  eq,
  opp,
) where

import Data.List (intercalate, nub, tails)
import Data.List.NonEmpty (NonEmpty ((:|)), nonEmpty)

data Finitary a = Finite a | Cofinite a deriving (Eq, Ord, Show, Functor)

newtype Intersection a = Intersection [Finitary a] deriving (Eq, Ord, Show, Functor)

newtype Times a = Times (NonEmpty (Intersection a)) deriving (Eq, Ord, Show, Functor)
newtype Union a = Union [Times a] deriving (Eq, Ord, Show, Functor)

empty1 :: Union a
empty1 = Union []

--- 1-dimensional U
univ1 :: (Ord a) => Union a
univ1 = single $ Intersection []

--- Internal computations
-- NOT to be exported, helper-functions for internal algebra-calculations
class InternalAlgebra t where
  -- Each type is responsible for one of these, the rest propagates:
  single :: (Ord a) => t a -> Union a
  compl' :: (Ord a) => t a -> Union a -- Finitary
  (/\) :: (Ord a) => t a -> t a -> Union a -- Intersection
  (><) :: (Ord a) => t a -> t a -> Union a -- Times
  (\/) :: (Ord a) => t a -> t a -> Union a -- Union

eq :: (Eq a) => Finitary a -> Finitary a -> Bool
Finite x `eq` Finite y = x == y
Cofinite x `eq` Cofinite y = x == y
_ `eq` _ = False

opp :: (Eq a) => Finitary a -> Finitary a -> Bool
Finite x `opp` Cofinite y = x == y
Cofinite x `opp` Finite y = x == y
_ `opp` _ = False

instance InternalAlgebra Finitary where
  single x = single $ Intersection [x]

  compl' (Finite x) = single $ Cofinite x
  compl' (Cofinite x) = single $ Finite x

  x /\ y | x `eq` y = single x
  x /\ y | x `opp` y = empty1
  x /\ y = single x /\ single y
  x >< y = single x >< single y
  x \/ y | x `eq` y = single x
  x \/ y | x `opp` y = univ1
  x \/ y = single x \/ single y

instance InternalAlgebra Intersection where
  single x = single $ Times $ x :| []

  -- Intersection should handle Univ-rules
  compl' (Intersection []) = empty1
  -- (21), i.e. DeMorgan
  compl' (Intersection (x : xs)) = compl' x \/ compl' (Intersection xs)

  -- Note that xs/ys = [] acts as univ Union here!
  Intersection xs /\ Intersection ys | True `elem` isOp = empty1
    where
      isOp = [x `opp` y | (x : zs) <- tails (xs <> ys), y <- zs]
  Intersection xs /\ Intersection ys = single $ Intersection $ nub $ xs <> ys

  x >< y = single $ Times $ x :| [y]

  Intersection [] \/ _ = univ1
  _ \/ Intersection [] = univ1
  x \/ y = single x \/ single y

instance InternalAlgebra Times where
  single x = Union [x]

  -- (22)
  compl' (Times (x :| [])) = compl' x
  compl' (Times (x :| (y : ys))) =
    (compl' x >< univs)
      \/ (univ1 >< compl' (Times (y :| ys)))
    where
      univs = single $ Times $ (const $ Intersection []) <$> y :| ys

  -- (30)
  Times (x :| xs) /\ Times (y :| ys) = case (nonEmpty xs, nonEmpty ys) of
    (Nothing, Nothing) -> x /\ y
    (Just xs', Just ys') -> (x /\ y) >< (Times xs' /\ Times ys')
    (Nothing, Just _) -> error "Right product longer than left in intersection"
    (Just _, Nothing) -> error "Left product longer than right in intersection"

  Times xs >< Times ys = single $ Times (xs <> ys)

  x \/ y = single x \/ single y

instance InternalAlgebra Union where
  single = id -- Not needed
  -- DeMorgan

  compl' (Union []) = error "TODO: Need a way to determine dimension here..."
  compl' (Union [x]) = compl' x
  compl' (Union (x : xs)) = compl' x /\ compl' (Union xs)

  Union [] /\ _ = empty1
  _ /\ Union [] = empty1
  -- (28)-(29)
  Union [x] /\ Union ys = foldr (\/) empty1 xIntersections
    where
      xIntersections = map (x /\) ys
  Union (x : xs) /\ Union ys = (single x /\ Union ys) \/ (Union xs /\ Union ys)

  -- (31)-(32) + emptyUnion products
  Union [] >< _ = empty1
  _ >< Union [] = empty1
  Union (x : xs) >< Union (y : ys) =
    (x >< y)
      \/ (Union [x] >< Union ys)
      \/ (Union xs >< Union [y])
      \/ (Union xs >< Union ys)

  -- Note that xs/ys = [] acts as empty-set, so these lines are technically unecessary
  x \/ Union [] = x
  Union [] \/ x = x
  -- Filter univs away here
  Union xs \/ Union ys
    | hasUnivs = univs
    | otherwise = Union $ nub $ xs <> ys
    where
      hasUnivs = any isUniv xs || any isUniv ys
      isUniv (Times zs) = all (\(Intersection is) -> null is) zs
      univs = single $ Times $ (const $ Intersection []) <$> ps
      Times ps = xs !! 0

--- First arg: Coordinate of removed val
proj :: (Ord a) => Int -> Union a -> Union a
-- Empty union.
-- NOTE: Maybe proj on Ø should be an error instead?
proj i _ | i < 1 = error "Projection index under 1"
proj _ (Union []) = empty1
-- First product has dim 1, so all products have dim 1, so projection is empty
proj _ (Union (Times (_ :| []) : _)) = error "One-dim product not allowed"
-- By invariant that dims of xs are constant, _all_ dims are > 1 here.
proj i (Union xs) = foldr (\/) empty1 (map (projProd i) xs)

projProd :: (Ord a) => Int -> Times a -> Union a
projProd i _ | i < 1 = error "projProd on index < 1"
projProd 2 (Times (_ :| [])) = error "projProd index too large for list"
projProd 2 (Times (x :| _ : ys)) = single $ Times $ x :| ys
projProd _ (Times (_ :| [])) = error "Projuction-index too large for projProd"
projProd 1 (Times (_ :| y : ys)) = single $ Times $ y :| ys
projProd i (Times (x :| y : ys)) = single x >< projProd (i - 1) (Times $ y :| ys)

diag :: (Ord a) => Union a -> Union a
diag (Union []) = Union []
diag (Union xs) = foldr (\/) empty1 (map diagProd xs)

diagProd :: (Ord a) => Times a -> Union a
diagProd (Times (_ :| [])) = error "Term-constructor should prevent diag on dim=1"
diagProd (Times (Intersection xs :| Intersection ys : zs)) =
  single $ Times (Intersection (xs <> ys) :| zs)

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

instance (PrettyShow a) => PrettyShow (Times a) where
  pshow (Times (x :| [])) = pshow x
  pshow (Times (x :| xs)) = withParens $ withOp " × " (x : xs)

instance (PrettyShow a) => PrettyShow (Union a) where
  pshow (Union []) = "∅"
  pshow (Union [x]) = pshow x
  pshow (Union xs) = withOp " ∪ " xs

pprint :: (PrettyShow a) => a -> IO ()
pprint = putStrLn . pshow
