module Tests (tests) where

import Test.QuickCheck
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, assertFailure, testCase, (@?=))
import Test.Tasty.QuickCheck (testProperty)

tests = testCase "failing" $ assertBool False
