{-# LANGUAGE GHC2024 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Main where

import Term

-- Example 1:
s1 :: Term 1 String
s1 = finite "s1"
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

exP :: Term 2 String
exP = finite "S1" >< finite "T1"

exQ :: Term 2 String
exQ = (finite "S2" >< finite "T2") \/ (finite "S3" >< finite "T3")

exR :: Term 2 String
exR = (finite "R1" >< cofinite "R2") /\ (cofinite "L1" >< finite "L2")

test1 :: Term 2 String
test1 = complement p

test2 :: Term 2 String
test2 = complement p /\ q

main :: IO ()
main = do
  pprint $ test2
  pprint $ diag test2
  pprint $ proj test2
  print $ eval $ proj test2

  print $ eval test2
