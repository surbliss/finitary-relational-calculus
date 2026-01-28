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

main :: IO ()
main = do
  pprint $ complement p
  pprint $ complement p /\ q
  print $ eval $ p
  print $ eval $ q
  print $ eval $ complement p
  print $ eval $ complement p /\ q
