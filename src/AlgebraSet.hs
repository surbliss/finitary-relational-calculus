{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE PatternSynonyms #-}

{- | Internal constructors that maintain ordering of algebra terms.
Not to be exported directly, but to be used internally only
-}
module AlgebraSet
where

-- (
--   Base (..)
--   , Product (..)
-- Finitary (..),
-- Intersection (..),
-- Product (..),
-- Union (..),
-- InternalAlgebra (..),
-- PrettyShow (..),
-- pprint,
-- empty,
-- univ1,
-- perm,
-- proj,
-- diag,
-- )

-- import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty ((:|)), nonEmpty, toList)

import Data.List.NonEmpty qualified as NE
import Data.Set (Set)
import Data.Set qualified as Set

-- data Base a = With (Set a) | Without (Set a) deriving (Eq, Show)

-- newtype Product a = Product (NonEmpty (Base a)) deriving (Eq, Show)

data Base a = With (Set a) | Without (Set a) deriving (Eq, Show)

data SetAlgebra a where
  Base :: Base a -> SetAlgebra a
  Product :: NonEmpty (SetAlgebra a) -> SetAlgebra a
  Union :: NonEmpty (SetAlgebra a) -> SetAlgebra a
  deriving (Eq, Show)

-- single :: SetAlgebra a -> SetAlgebra a
-- single (With x) = Union $ Product (With x :| []) :| []
-- single (Without x) = Union $ Product (Without x :| []) :| []
-- single _ = error "Illegal use of single, on Product or Union"

fins :: (Ord a) => [a] -> SetAlgebra a
fins xs = Base $ With $ Set.fromList xs

empty1 :: SetAlgebra a
empty1 = Base $ With Set.empty

--- 1-dimensional U
univ1 :: SetAlgebra a
univ1 = Base $ Without Set.empty

isEmpty :: SetAlgebra a -> Bool
isEmpty (Base (Without _)) = False
isEmpty (Base (With x)) = Set.null x
isEmpty (Product xs) = any isEmpty xs
isEmpty (Union xs) = all isEmpty xs

isUniv :: SetAlgebra a -> Bool
isUniv (Base (With _)) = False
isUniv (Base (Without x)) = Set.null x
isUniv (Product xs) = all isUniv xs
isUniv (Union xs) = any isUniv xs

compl :: (Ord a, Show a) => SetAlgebra a -> SetAlgebra a
compl (Base (With x)) = Base $ Without x
compl (Base (Without x)) = Base $ With x
compl (Product (x :| [])) = compl x
compl (Product (x :| y : ys)) =
  (compl x >< univ1)
    \/ (univ1 >< compl (Product (y :| ys)))
compl (Union (x :| [])) = compl x
compl (Union (x :| y : ys)) = compl x /\ compl (Union (y :| ys))

(/\) :: (Ord a) => SetAlgebra a -> SetAlgebra a -> SetAlgebra a
--- First, all possible errors
Base _ /\ Product (_ :| _) = error "inter base prod"
Product (_ :| _) /\ Base _ = error "inter prod base"
Product (x :| []) /\ Product (y :| []) = x /\ y
Product (_ :| []) /\ Product (_ :| _) = error "inter prod"
Product (_ :| _) /\ Product (_ :| []) = error "inter prod"
--- Empty/Univ checking:
x /\ _ | isEmpty x = x
_ /\ y | isEmpty y = y
x /\ y | isUniv x = y
x /\ y | isUniv y = x
Base (With x) /\ Base (With y) = Base $ With $ Set.intersection x y
Base (With x) /\ Base (Without y) = Base $ With $ x Set.\\ y
Base (Without x) /\ Base (With y) = Base $ With $ y Set.\\ x
Base (Without x) /\ Base (Without y) = Base $ Without $ Set.union x y
-- No base /\ non-triv product
-- All product /\ product situatuions
Product (x :| x' : xs) /\ Product (y :| y' : ys) = (x /\ y) >< (Product (x' :| xs) /\ Product (y' :| ys))
-- Second term is now not a product. Move intersections down
Product (x :| []) /\ y = x /\ y
x /\ Product (y :| []) = x /\ y
Union (x :| []) /\ y = x /\ y
x /\ Union (y :| []) = x /\ y
Union (x :| x' : xs) /\ y = (x /\ y) \/ (x /\ Union (x' :| xs))
x /\ Union (y :| y' : ys) = (x /\ y) \/ (x /\ Union (y' :| ys))

(\/) :: (Ord a) => SetAlgebra a -> SetAlgebra a -> SetAlgebra a
Base _ \/ Product (_ :| _) = error "union base prod"
Product (_ :| _) \/ Base _ = error "union prod base"
-- All Product \/ Product situations
Product (x :| []) \/ Product (y :| []) = x \/ y
Product (_ :| _) \/ Product (_ :| []) = error "union prod"
Product (_ :| []) \/ Product (_ :| _) = error "union prod"
x \/ y | isEmpty x = y
x \/ y | isEmpty y = x
x \/ _ | isUniv x = x
_ \/ x | isUniv x = x
Base (With x) \/ Base (With y) = Base $ With $ Set.union x y
Base (With x) \/ Base (Without y) = Base $ Without $ y Set.\\ x
Base (Without x) \/ Base (With y) = Base $ Without $ x Set.\\ y
Base (Without x) \/ Base (Without y) = Base $ Without $ Set.intersection x y
-- No base /\ non-triv product
--- Formal union
Union (x :| []) \/ y = x \/ y
x \/ Union (y :| []) = x \/ y
xs@(Product _) \/ ys@(Product _) = Union $ xs :| [ys]
Union xs \/ Union ys = Union $ xs <> ys
Union (x :| xs) \/ y = Union (x :| xs <> [y])
x \/ Union (y :| ys) = Union (x :| y : ys)

-- Unions

(><) :: SetAlgebra a -> SetAlgebra a -> SetAlgebra a
x >< y
  | isEmpty x || isEmpty y = empty1 >< empty1
  | otherwise = Product (x :| [y])

-- --- Internal computations
-- -- NOT to be exported, helper-functions for internal algebra-calculations
-- class InternalAlgebra t where
--   -- Each type is responsible for one of these, the rest propagates:
--   single :: t a -> Product a
--   compl' :: t a -> Product a
--   (/\) :: t a -> t a -> Product a
--   (><) :: t a -> t a -> Product a
--   (\/) :: t a -> t a -> Product a
--   (//) :: t a -> t a -> Product a
--   x // y = x /\ complement y

-- instance InternalAlgebra Intersection where
--   single x = single $ Product $ x :| []

--   -- Intersection should handle Univ-rules
--   compl' (Intersection []) = empty
--   -- (21), i.e. DeMorgan
--   compl' (Intersection (x : xs)) = compl' x \/ compl' (Intersection xs)

--   -- Note that xs/ys = [] acts asunivUnion here!
--   Intersection xs /\ Intersection ys = single $ Intersection $ xs <> ys

--   x >< y = single $ Product $ x :| [y]

--   Intersection [] \/ _ = univ1
--   _ \/ Intersection [] = univ1
--   x \/ y = single x \/ single y

-- instance InternalAlgebra Product where
--   single x = Union [x]

--   -- (22)
--   compl' (Product (x :| [])) = compl' x
--   compl' (Product (x :| (y : ys))) =
--     (compl' x >< univs)
--       \/ (univ1 >< compl' (Product (y :| ys)))
--     where
--       univs = single $ Product $ NE.map (const $ Intersection []) $ y :| ys

--   -- (30)
--   Product (x :| xs) /\ Product (y :| ys) = case (nonEmpty xs, nonEmpty ys) of
--     (Nothing, Nothing) -> x /\ y
--     (Just xs', Just ys') -> (x /\ y) >< (Product xs' /\ Product ys')
--     (Nothing, Just _) -> error "Right product longer than left in intersection"
--     (Just _, Nothing) -> error "Left product longer than right in intersection"

--   Product xs >< Product ys = single $ Product (xs <> ys)

--   x \/ y = single x \/ single y

-- instance InternalAlgebra Union where
--   single = id -- Not needed
--   -- DeMorgan

--   compl' (Union []) = error "TODO: Need a way to determine dimension here..."
--   compl' (Union [x]) = compl' x
--   compl' (Union (x : xs)) = compl' x /\ compl' (Union xs)

--   Union [] /\ _ = empty
--   _ /\ Union [] = empty
--   -- (28)-(29)
--   Union [x] /\ Union ys = foldl (\/) empty xIntersections
--     where
--       xIntersections = map (x /\) ys
--   Union (x : xs) /\ Union ys = (single x /\ Union ys) \/ (Union xs /\ Union ys)

--   -- Union [x] /\ Union (y : ys) = (x /\ y) \/ single x /\ Union ys
--   -- Union (x : xs) /\ Union (y : ys) =
--   --   (x /\ y)
--   --     \/ (single x /\ Union ys)
--   --     \/ (Union xs /\ single y)
--   --     \/ (Union xs /\ Union ys)

--   -- (31)-(32) + emptyUnion products
--   Union [] >< _ = empty
--   _ >< Union [] = empty
--   Union (x : xs) >< Union (y : ys) =
--     (x >< y)
--       \/ (Union [x] >< Union ys)
--       \/ (Union xs >< Union [y])
--       \/ (Union xs >< Union ys)

--   -- Note that xs/ys = [] acts as empty-set, so these lines are technically unecessary
--   x \/ Union [] = x
--   Union [] \/ x = x
--   -- Filter univs away here! I.e. 1 x 1 x 1
--   -- WRONG: Should not filter univs, should turn everything _into_ univ!
--   Union xs \/ Union ys
--     | hasUnivs = univs
--     | otherwise = Union $ xs <> ys
--     where
--       hasUnivs = any isUniv xs || any isUniv ys
--       isUniv (Product zs) = all (\(Intersection is) -> null is) zs
--       univs = single $ Product $ NE.map (const $ Intersection []) $ ps
--       Product ps = xs !! 0

-- --- Relational algegra-functions
-- perm :: [Int] -> Union a -> Union a
-- perm = undefined

-- --- First arg: Coordinate of removed val
-- proj :: Int -> Union a -> Union a
-- -- Empty union.
-- -- NOTE: Maybe proj on Ø should be an error instead? Hm
-- proj i _ | i < 1 = error "Projection index under 1"
-- proj _ (Union []) = empty
-- -- First product has dim 1, so all products have dim 1, so projection is empty
-- proj _ (Union (Product (_ :| []) : _)) = error "One-dim product not allowed"
-- -- By invariant that dims of xs are constant, _all_ dims are > 1 here.
-- proj i (Union xs) = foldl (\/) empty (map (projProd i) xs)

-- projProd :: Int -> Product a -> Union a
-- projProd i _ | i < 1 = error "projProd on index < 1"
-- projProd 2 (Product (x :| [])) = error "projProd index too large for list"
-- projProd 2 (Product (x :| y : ys)) = single $ Product $ x :| ys
-- projProd i (Product (_ :| [])) = error "Projuction-index too large for projProd"
-- projProd 1 (Product (_ :| y : ys)) = single $ Product $ y :| ys
-- projProd i (Product (x :| y : ys)) = single x >< projProd (i - 1) (Product $ y :| ys)

-- diag :: Union a -> Union a
-- diag (Union []) = Union []
-- diag (Union xs) = foldl (\/) empty (map diagProd xs)

-- -- TODO: Normalize, to remove potential 'univs'
-- diagProd :: Product a -> Union a
-- diagProd (Product (_ :| [])) = error "Term-constructor should prevent diag on dim=1"
-- diagProd (Product (Intersection xs :| Intersection ys : zs)) =
--   single $ Product (Intersection (xs <> ys) :| zs)

-- ---------------------------------------------------

-- -- Pretty-printing
-- ---------------------------------------------------
-- class PrettyShow a where
--   pshow :: a -> String

-- withOp :: (PrettyShow a) => String -> [a] -> String
-- withOp op xs = intercalate op (map pshow xs)

-- withParens :: String -> String
-- withParens s = "(" ++ s ++ ")"

-- instance PrettyShow String where
--   pshow xs = xs

-- instance PrettyShow Int where
--   pshow xs = show xs

-- instance (PrettyShow a) => PrettyShow (Finitary a) where
--   pshow (Finite x) = pshow x
--   pshow (Cofinite x) = pshow x ++ "ᶜ"

-- instance (PrettyShow a) => PrettyShow (Intersection a) where
--   pshow (Intersection []) = "𝕌"
--   pshow (Intersection [x]) = pshow x
--   pshow (Intersection xs) = withOp "∩" xs

-- instance (PrettyShow a) => PrettyShow (Product a) where
--   pshow (Product (x :| [])) = pshow x
--   pshow (Product xs) = withParens $ withOp " × " (toList xs)

-- instance (PrettyShow a) => PrettyShow (Union a) where
--   pshow (Union []) = "∅"
--   pshow (Union [x]) = pshow x
--   pshow (Union xs) = withOp " ∪ " xs

-- pprint :: (PrettyShow a) => a -> IO ()
-- pprint = putStrLn . pshow
