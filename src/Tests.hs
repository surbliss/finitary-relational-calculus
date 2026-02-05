{-# LANGUAGE GHC2024 #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Tests (tests) where

-- import Finitary

import GHC.TypeLits
import Test.QuickCheck hiding ((><))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, assertFailure, testCase, (@?=))
import Test.Tasty.QuickCheck (testProperty)

-- import Eval
import Term

-- Properties to be tested

rewrite20 :: (Eq a, Ord a) => Term n a -> Bool
rewrite20 c = eval (complement (complement c)) == eval c

rewrite21 :: (Eq a, Ord a) => Term n a -> Term n a -> Bool
rewrite21 c d = eval (complement (c /\ d)) == eval (complement c \/ complement d)

-- TODO: Requires univ-magic
-- rewrite22 :: (Eq a, Ord a) => Term n a -> Term n a -> Bool
-- rewrite22 c d = eval (complement (c >< d)) == (complement c >< univ) \/ (univ >< complement d)

rewrite23 :: (Eq a, Ord a) => Term n a -> Term n a -> Bool
rewrite23 c d = eval (complement (c \/ d)) == eval (complement c /\ complement d)

-- No need to eval here ('empty' has canonical representation)
rewrite24 :: (Eq a, Ord a) => Term (n + 1) a -> Bool
rewrite24 c = c /\ empty == empty

rewrite25 :: (Eq a, Ord a) => Term (n + 1) a -> Bool
rewrite25 d = empty /\ d == empty

-- TODO: Need way to determine 'univ' size
-- rewrite26 :: (Eq a, Ord a) => Term (n + 1) a -> Bool
-- rewrite26 c = c /\ univ == c

-- rewrite27 :: (Eq a, Ord a) => Term (n + 1) a -> Bool
-- rewrite27 d = univ /\ d == d

rewrite28 :: (Eq a, Ord a) => Term n a -> Term n a -> Term n a -> Bool
rewrite28 c d e = eval (c /\ (d \/ e)) == eval ((c /\ d) \/ (c /\ e))

rewrite29 :: (Eq a, Ord a) => Term n a -> Term n a -> Term n a -> Bool
rewrite29 c d e = eval ((c \/ d) /\ e) == eval ((c /\ e) \/ (d /\ e))

rewrite30 :: (Eq a, Ord a) => Term n a -> Term n a -> Term n a -> Term n a -> Bool
rewrite30 c d e f = eval ((c >< d) /\ (e >< f)) == eval ((c /\ e) >< (d /\ f))

rewrite31 :: (Eq a, Ord a) => Term n a -> Term n a -> Term n a -> Bool
rewrite31 c d e = eval (c >< (d \/ e)) == eval ((c >< d) \/ (c >< e))

rewrite32 :: (Eq a, Ord a) => Term n a -> Term n a -> Term n a -> Bool
rewrite32 c d e = eval ((c \/ d) >< e) == eval ((c >< e) \/ (d >< e))

--- Generators
-- gen1DimTerm :: Gen (Term 1 String)
-- gen1DimTerm = undefined

-- prop_rewrite20 :: (Eq a, Ord a) => Term n a -> Property
-- prop_rewrite20 = undefined

-- Helpers
-- eq :: (Eq a, Show a, Ord a) => Term n a -> Term n a -> TestTree
-- eq t s = testCase "" $ (eval t) @?= (eval s)

-- (@?/=) :: (Eq a) => a -> a -> Assertion
-- x @?/= y = assertBool "" $ x /= y

exP :: Term 2 String
exP = finite "S1" >< finite "T1"

exQ :: Term 2 String
exQ = (finite "S2" >< finite "T2") \/ (finite "S3" >< finite "T3")

exR :: Term 2 String
exR = (finite "R1" >< cofinite "R2") /\ (cofinite "L1" >< finite "L2")

testBool :: Bool -> TestTree
testBool b = testCase "" $ assertBool "" b

-- Algebra-tests
-- Finitary
termTests :: TestTree
termTests =
  testGroup "Finitary Tests" $
    [ testBool $ rewrite20 exQ
    , testBool $ rewrite20 exP
    , testBool $ rewrite21 exP exP
    , testBool $ rewrite21 exP exQ
    , testBool $ rewrite21 exQ exP
    , testBool $ rewrite21 exQ exQ
    , testBool $ rewrite23 exP exP
    , testBool $ rewrite23 exP exQ
    , testBool $ rewrite23 exQ exP
    , testBool $ rewrite23 exQ exQ
    , testBool $ rewrite24 exP
    , testBool $ rewrite24 exQ
    , testBool $ rewrite24 exR
    , testBool $ rewrite25 exP
    , testBool $ rewrite25 exQ
    , testBool $ rewrite25 exR
    , testBool $ rewrite28 exQ exP exR
    , testBool $ rewrite28 exQ exR exP
    , testBool $ rewrite28 exP exQ exR
    , testBool $ rewrite28 exP exR exQ
    , testBool $ rewrite28 exR exQ exP
    , testBool $ rewrite28 exR exQ exP
    , testBool $ rewrite29 exQ exP exR
    , testBool $ rewrite29 exQ exR exP
    , testBool $ rewrite29 exP exQ exR
    , testBool $ rewrite29 exP exR exQ
    , testBool $ rewrite29 exR exQ exP
    , testBool $ rewrite29 exR exQ exP
    , testBool $ rewrite30 exQ exP exR exP
    , testBool $ rewrite30 exQ exR exP exQ
    , testBool $ rewrite30 exP exQ exR exR
    , testBool $ rewrite30 exP exR exQ exP
    , testBool $ rewrite30 exR exQ exP exQ
    , testBool $ rewrite30 exR exQ exP exR
    , testBool $ rewrite31 exQ exP exR
    , testBool $ rewrite31 exQ exR exP
    , testBool $ rewrite31 exP exQ exR
    , testBool $ rewrite31 exP exR exQ
    , testBool $ rewrite31 exR exQ exP
    , testBool $ rewrite31 exR exQ exP
    , testBool $ rewrite32 exQ exP exR
    , testBool $ rewrite32 exQ exR exP
    , testBool $ rewrite32 exP exQ exR
    , testBool $ rewrite32 exP exR exQ
    , testBool $ rewrite32 exR exQ exP
    , testBool $ rewrite32 exR exQ exP
    -- , complement (complement exQ) @?= exQ
    -- , complement (exP /\ exQ) @?= (complement exP) \/ (complement exQ)
    ]

tests :: TestTree
tests = testGroup "All tests" $ [termTests]
