module Tests (tests) where

import Data.Set
import Finitary
import Test.QuickCheck
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, assertFailure, testCase, (@?=))
import Test.Tasty.QuickCheck (testProperty)

-- For repl work
-- base :: (Ord a) => [a] -> Algebra a
-- base xs = Base $ Finite $ fromList xs

tests = testCase "" $ True @?= True
