{-# LANGUAGE GHC2024 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Main where

import Data.List.NonEmpty (NonEmpty ((:|)))
import Data.List.NonEmpty qualified as NE
import Data.Set
import Finitary

-- Example 1:
s1 :: Term 1 String
s1 = finite "s12"
s2 :: Term 1 String
s2 = finite "s2"
s3 :: Term 1 String
s3 = finite "s3"
t1 :: Term 1 String
t1 = finite "t1"
t2 :: Term 1 String
t2 = finite "t2"
t3 :: Term 1 String
t3 = finite "t3"

p :: Term 2 String
p = s1 >< t1

q :: Term 2 String
q = (s2 >< t2) \/ (s3 >< t3)

u :: Intersection (Set Int)
u = Intersection []

fin :: (Ord a) => [a] -> Finitary (Set a)
fin is = Finite $ fromList is
x :: Finitary (Set Int)
x = fin [1]
y :: Finitary (Set Int)
y = fin [2, 3, 4]
z :: Finitary (Set Int)
z = fin [3, 4, 5]

inter1 :: Intersection (Set Int)
inter1 = Intersection [x]

inter2 :: Intersection (Set Int)
inter2 = Intersection [y, z]

prod :: Product (Set Int)
prod = Product $ Intersection [x] :| [Intersection [y, z]]
  where

main :: IO ()
main = do
  -- pprint $ complement p /\ q
  print "hello"

-- print $ evalIntersection inter2

-- Shound be: Just $ Finite ([1,3], [1,4])
