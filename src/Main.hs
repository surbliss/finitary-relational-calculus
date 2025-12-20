{-# LANGUAGE GHC2024 #-}

module Main where

import Data.Set
import Finitary

-- import Data.Vector.Sized
-- import GHC.TypeLits (type (+))

---------------------------------------------------
-- Data structures
---------------------------------------------------
-- Free to choose implementation of a seen fit
-- data Finitary f a where
--   Empty :: Finitary f a
--   -- For finite-cofin algebra, all singletons are available
--   -- FSingleton :: a -> Finitary f a
--   FSet :: f a -> Finitary f a
--   (:\/) :: Finitary f a -> Finitary f a -> Finitary f a
--   (:/\) :: Finitary f a -> Finitary f a -> Finitary f a
--   (:~~) :: Finitary f a -> Finitary f a -> Finitary f a
--   Co :: Finitary f a -> Finitary f a

-- ---------------------------------------------------
-- -- Reducing expressions
-- ---------------------------------------------------
-- -- Helper functions that correspond to data-constructors, but reduce away
-- -- Empty/Universal sets. Also, get rid of any cosets
-- (\/) :: Finitary f a -> Finitary f a -> Finitary f a
-- s \/ Empty = s
-- Empty \/ s = s
-- (Co s) \/ (Co t) = compl (s /\ t)
-- (Co s) \/ t = compl (s ~~ t)
-- s \/ (Co t) = compl (t ~~ s)
-- s \/ t = s :\/ t

-- (/\) :: Finitary f a -> Finitary f a -> Finitary f a
-- _ /\ Empty = Empty
-- Empty /\ _ = Empty
-- (Co s) /\ (Co t) = compl (s \/ t)
-- (Co s) /\ t = t ~~ s
-- s /\ (Co t) = (s ~~ t)
-- s /\ t = s :/\ t

-- (~~) :: Finitary f a -> Finitary f a -> Finitary f a
-- Empty ~~ _ = Empty
-- s ~~ Empty = s
-- (Co s) ~~ (Co t) = t ~~ s
-- s ~~ (Co t) = s /\ t
-- -- s ~~ t = s :~~ t
-- s ~~ t = s /\ compl t

-- compl :: Finitary f a -> Finitary f a
-- compl (Co s) = s
-- compl s = Co s

-- -- Rewrite rules (Figure 2)
-- reduce :: Finitary f a -> Finitary f a
-- reduce (x :\/ y) = reduce x \/ reduce y
-- reduce (x :/\ y) = reduce x /\ reduce y
-- reduce (x :~~ y) = reduce x ~~ reduce y
-- reduce (Co x) = compl (reduce x)
-- reduce (FSet x) = FSet x
-- reduce (Empty) = Empty

main :: IO ()
main = do
  putTextLn "Hello (from boolean-database)"
  putTextLn $ show $ Finite $ singleton (2 :: Int)

---------------------------------------------------
-- Debug stuff
---------------------------------------------------
-- instance {-# OVERLAPPABLE #-} Show (Finitary f a) where
--   show Empty = "Empty"
--   show (Co Empty) = "Univ"
--   -- show (FSingleton _) = "{.}"
--   show (FSet _) = "{...}"
--   show (x :\/ y) = show x ++ "U" ++ show y
--   show (x :/\ y) = show x ++ "N" ++ show y
--   show (x :~~ y) = show x ++ "-" ++ show y
--   show (Co x) = show x ++ "^c"

-- instance (Show a) => Show (Finitary [] a) where
--   show Empty = "Empty"
--   show (Co Empty) = "Univ"
--   -- show (FSingleton x) = "{" ++ show x ++ "}"
--   show (FSet xs) = "{" ++ intersperse ' ' (concatMap show xs) ++ "}"
--   show (x :\/ y) = show x ++ " + " ++ show y
--   show (x :/\ y) = "(" ++ show x ++ " * " ++ show y ++ ")"
--   show (x :~~ y) = "(" ++ show x ++ " -- " ++ show y ++ ")"
--   show (Co x) = show x ++ "^c"

-- -- Claude tests
{-
-- Triple complement
reduce (Co (Co (Co (FSet [1,2]))))

-- Nested De Morgan
reduce (Co ((FSet [1]) :/\ (FSet [2])))

-- Deep nesting with alternating ops
reduce (Co ((Co (FSet [1]) :\/ FSet [2]) :/\ (FSet [3] :\/ Co (FSet [4]))))

-- Self-intersection with complement
reduce ((FSet [1,2]) :/\ Co (FSet [1,2]))

-- Difference of complements
reduce (Co (FSet [1]) :~~ Co (FSet [2]))
-}
