{-# LANGUAGE GHC2024 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Main where

import Dict.Algebra
import PrettyShow

fin :: [Int] -> Relation
fin = finite

-- --- Sus query: 1 (because -1 rated 10 and 11 the same)
-- All brands
susB :: Relation
susB = fin [1, 2, 3]

-- Brand 2 and brand 3 _both_ cell 30?
susP :: Relation
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

-- Product >< UserID >< review
-- User -1 hates brand 2. User -2 loves brand 1
susS :: Relation
susS = (fin [20, 21, 22] >< pairs [(-1, 0)]) \/ (fin [30, 31, 32] >< pairs [(-2, 10)])

main :: IO ()
main = do
  putStrLn "----"
  pprint $ (susP >< univ >< univ) ==> (univ >< susS)
