{-# LANGUAGE GHC2024 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Main where

import Set.Query

--- Sus query
-- Coord 1:Brands, 2:Products, 3:User, 4:Score
-- B sub 1, P sub 1 x 2, S sub 2 x 3 x 4
-- B(b=1), P(b=1, p=2), S(p=2, u=3, s=4)
-- Solution : B /\ pi_u,s $ compl $ pi_p $ P >< 1 >< 1 /\ compl (1 >< S)

-- --- Sus query: 1 (because -1 rated 10 and 11 the same)
-- All brands
susB :: Query
susB = fins 1 [1, 2, 3]

-- Brand 2 and brand 3 _both_ cell 30?
susP :: Query
susP =
  pairs
    2
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
susP2 :: Query
susP2 = (fin (1, 1) :/\ fins 2 [10, 11]) :\/ (fin (1, 2) :/\ fins 2 [20, 21, 22]) :\/ (fin (1, 3) :/\ fins 2 [30, 31, 32])

-- Product >< UserID >< review
-- User -1 hates brand 2. User -2 loves brand 1
susS :: Query
susS =
  (fins 2 [20, 21, 22] :/\ pairs 3 [(-1, 0)])
    :\/ (fins 2 [30, 31, 32] :/\ pairs 3 [(-2, 10)])

--- Compute sus query
-- B, P, S
-- sus :: Query -> Query -> Query -> Query
-- sus b p s = b /\ (exists 2 $ exists 2 $ forAll 2 $ (p >< univ >< univ) --> (univ >< s))

-- sus b p s = b /\ (proj 2 $ proj 2 $ compl $ proj 2 $ (p >< univ >< univ) /\ (univ >< compl s))

main :: IO ()
main = do
  -- pprint $ compl $ proj 2 $ (susP >< univ >< univ ) /\ (univ >< compl susS)
  putStrLn "----"
  -- print $ member (1, 3) $ susB :/\ susP --> susS
  -- print $ susP
  print $ (2, 21) `member` susS
  print susS
  print $ simp $ (proj 4 $ C $ proj 2 $ susP --> susS)
  putStrLn "---"
  let sus = susB :/\ (proj 3 $ proj 4 $ C $ proj 2 $ susP --> susS)
  print sus
  print $ member (1, 3) $ susB :/\ (proj 3 $ proj 4 $ C $ proj 2 $ susP --> susS)
