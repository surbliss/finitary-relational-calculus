{-# LANGUAGE GHC2024 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Main where

import PrettyShow
import Set.Term

-- --- Sus query: 1 (because -1 rated 10 and 11 the same)
-- All brands
susB :: Term 1
susB = fins [1, 2, 3]

-- Brand 2 and brand 3 _both_ cell 30?
susP :: Term 2
susP = pairs [(1, 10), (1, 11), (2, 20), (2, 21), (2, 22), (2, 30), (3, 30), (3, 31), (3, 32)]

-- Product >< UserID >< review
-- User -1 hates brand 2. User -2 loves brand 1
susS :: Term 3
susS = (fins [20, 21, 22] >< pairs [(-1, 0)]) \/ (fins [30, 31, 32] >< pairs [(-2, 10)])

main :: IO ()
main = do
  putStrLn "----"
  pprint $ exists 2 $ exists 2 $ forAll 2 $ (susP >< univ >< univ) ==> (univ >< susS)
