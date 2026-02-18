{-# LANGUAGE GHC2024 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Main where

import PrettyShow
import Set.Term

-- Example 1:
s1 :: Term 1
s1 = fin 10
s2 :: Term 1
s2 = fin 20
s3 :: Term 1
s3 = fin 30
t1 :: Term 1
t1 = fin 1
t2 :: Term 1
t2 = fin 2
t3 :: Term 1
t3 = fin 3

r1 :: Term 1
r1 = fin 100
r2 :: Term 1
r2 = fin 200
l1 :: Term 1
l1 = fin 1000
l2 :: Term 1
l2 = fin 2000

exP :: Term 2
exP = s1 >< t1

exQ :: Term 2
exQ = (s2 >< t2) \/ (s3 >< t3)

exR :: Term 2
exR = (r1 >< compl r2) /\ (compl l1 >< l2)

--- Sus query
-- Coord 1:Brands, 2:Products, 3:User, 4:Score
-- B sub 1, P sub 1 x 2, S sub 2 x 3 x 4
-- B(b=1), P(b=1, p=2), S(p=2, u=3, s=4)
-- Solution : B /\ pi_u,s $ compl $ pi_p $ P >< 1 >< 1 /\ compl (1 >< S)

pairs :: [(Int, Int)] -> Term 2
pairs xs = foldl (\/) (empty >< empty) (map finProd xs)
  where
    finProd (x, y) = fin x >< fin y

triples :: [(Int, Int, Int)] -> Term 3
triples xs = foldl (\/) (empty >< empty >< empty) (map finProd xs)
  where
    finProd (x, y, z) = fin x >< fin y >< fin z

-- --- Sus query: 1 (because -1 rated 10 and 11 the same)
-- All brands
susB :: Term 1
susB = fins [1, 2, 3]

-- Brand 2 and brand 3 _both_ cell 30?
susP :: Term 2
susP =
  pairs
    [ (1, 10)
    , (1, 11)
    , (2, 20)
    , (2, 21)
    , (2, 22)
    , (2, 30)
    , (3, 30)
    , (3, 31)
    , (3, 32)
    ]

--- More compacly represented?
susP2 :: Term 2
susP2 = (fin 1 >< fins [10, 11]) \/ (fin 2 >< fins [20, 21, 22]) \/ (fin 3 >< fins [30, 31, 32])

-- Product >< UserID >< review
-- User -1 hates brand 2. User -2 loves brand 1
susS :: Term 3
susS =
  triples
    [ (20, -1, 0)
    , (21, -1, 0)
    , (22, -1, 0)
    , (30, -1, 0)
    , (30, -2, 10)
    , (31, -2, 10)
    , (32, -2, 10)
    ]

--- Compute sus query
-- B, P, S
sus :: Term 1 -> Term 2 -> Term 3 -> Term 1
sus b p s = b /\ (exists 2 $ exists 2 $ forAll 2 $ (p >< univ >< univ) --> (univ >< s))

-- sus b p s = b /\ (proj 2 $ proj 2 $ compl $ proj 2 $ (p >< univ >< univ) /\ (univ >< compl s))

main :: IO ()
main = do
  -- pprint $ compl $ proj 2 $ (susP >< univ >< univ ) /\ (univ >< compl susS)
  print "----"
  pprint $ susP
  pprint $ susP2
  pprint $ sus susB susP2 susS
  pprint $ sus susB susP2 susS
  pprint $ sus susB susP susS --- Muuuuuch slower (expectedly)
