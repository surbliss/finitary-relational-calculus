{-# LANGUAGE GHC2024 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Main where

import Set.Term

-- Example 1:
s1 :: Term 1 String
s1 = finite ["s1"]
s2 :: Term 1 String
s2 = finite ["s2"]
s3 :: Term 1 String
s3 = finite ["s3"]
t1 :: Term 1 String
t1 = finite ["t1"]
t2 :: Term 1 String
t2 = finite ["t2"]
t3 :: Term 1 String
t3 = finite ["t3"]

p :: Term 2 String
p = s1 >< t1

q :: Term 2 String
q = (s2 >< t2) \/ (s3 >< t3)

exP :: Term 2 String
exP = finite ["S1"] >< finite ["T1"]

exQ :: Term 2 String
exQ = (finite ["S2"] >< finite ["T2"]) \/ (finite ["S3"] >< finite ["T3"])

exR :: Term 2 String
exR = (finite ["R1"] >< cofinite ["R2"]) /\ (cofinite ["L1"] >< finite ["L2"])

--- Sus query
-- Coord 1:Brands, 2:Products, 3:User, 4:Score
-- B sub 1, P sub 1 x 2, S sub 2 x 3 x 4

-- fins :: (Eq a) => [a] -> Term 1 a
-- fins xs = foldl (\/) empty (map finite xs)

-- pairs :: (Ord a, Eq a) => [(a, a)] -> Term 2 a
-- pairs xs = foldl (\/) (empty1 >< empty1) (map finProd xs)
--   where
--     finProd (x, y) = finite x >< finite y

--- Brands
susB :: Term 1 String
susB = finite ["Tuborg", "Harboe", "Thomas' bryghus", "Pepsi"]

--- Products, for each brand. Each brand should have unique products (I think?)
susP :: Term 2 String
susP =
  finite ["Tuborg"]
    >< finite ["Tuborg classic", "Tuborg pilsner", "Squash"]
    \/ finite ["Harboe"]
    >< finite ["Harboe pilsner", "Harboe cola", "Harboe classic"]
    \/ finite ["Pepsi"]
    >< finite ["Pepsi cola", "Pepsi max"]

single :: (Ord a) => a -> Term 1 a
single x = finite [x]

pairs :: (Ord a) => [(a, a)] -> Term 2 a
pairs xs = foldl (\/) (empty >< empty) (map finProd xs)
  where
    finProd (x, y) = single x >< single y

-- Scores: Product + a User + their score
-- Suspicious brands: Tuborg (from Mr SuS) and Harboe (From Jens)
susS :: Term 3 String
susS =
  single "Tuborg classic"
    >< pairs [("Thomas", "3"), ("Mr Sus", "1"), ("Jens", "5")]
    \/ single "Tuborg classic"
    >< pairs [("Thomas", "4"), ("Mr Sus", "1"), ("Jens", "5")]
    \/ single "Squash"
    >< pairs [("Mr Sus", "1")]
    \/ single "Harboe pilsner"
    >< pairs [("Thomas", "10"), ("Jens", "5")]
    \/ single "Harboe cola"
    >< pairs [("Thomas", "2"), ("Jens", "5")]
    \/ single "Harboe classic"
    >< pairs [("Thomas", "1"), ("Jens", "5")]
    \/ single "Pepsi cola"
    >< pairs [("Thomas", "5")]
    \/ single "Pepsi max"
    >< pairs [("Thomas", "3")]

-- susQ :: Term 1 String
-- susQ = susB /\ rhs
--   where
--     rhs = proj 4 $ proj 3 $ complement $ proj 2 $ (susP >< univ >< univ) /\ (univ >< complement susS)

--- Building up, so we can test one inner term at a time

-- fin :: (Eq a) => a -> Term 1 a
-- fin = finite

-- --- Sus query: 1 (because -1 rated 10 and 11 the same)
susBB :: Term 1 Int
susBB = fins [1, 2]

susPP :: Term 2 Int
susPP = single 1 >< fins [10, 11] \/ single 2 >< fins [20]

susSS :: Term 3 Int
susSS =
  single 10
    >< pairs [(-1, 0)]
    \/ single 11
    >< pairs [(-1, 0)]

-- sus1 :: Term 4 Int
-- sus1 = (susPP >< univ >< univ) /\ (univ >< complement susSS)

-- -- Proj p
-- sus2 :: Term 3 Int
-- sus2 = proj 2 sus1

-- x :: Term 1 Int
-- x = fin 0
main :: IO ()
main = do
  -- Sus query:
  print "------"
  let l = susPP >< univ >< univ
  let r = univ >< compl susSS
  -- pprint l
  -- pprint r
  let inner = l /\ r
  -- pprint inner
  pprint $ inner
  pprint $ proj 2 $ inner
  let two = compl $ proj 2 $ inner
  print ""
  pprint $ compl $ l \/ l \/ l \/ l

-- let inner = l /\ r
