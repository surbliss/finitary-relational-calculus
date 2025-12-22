{-# LANGUAGE GHC2024 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Main where

import Data.Set

-- import Finitary
import Algebra

-- Example 1:
s1 :: Algebra String
s1 = set "s1"
s2 :: Algebra String
s2 = set "s2"
s3 :: Algebra String
s3 = set "s3"
t1 :: Algebra String
t1 = set "t1"
t2 :: Algebra String
t2 = set "t2"
t3 :: Algebra String
t3 = set "t3"

p :: Algebra String
p = s1 >< t1

q :: Algebra String
q = (s2 >< t2) \/ (s3 >< t3)

-- Pretty Show
pShow :: (Show a) => Algebra a -> String
pShow = undefined

main :: IO ()
main = do
  putStrLn $ show (compl p /\ q)

---------------------------------------------------
-- Debug stuff
---------------------------------------------------
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
