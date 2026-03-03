-- TODO: Find better solution than removing this warning...
{-# OPTIONS_GHC -Wno-orphans #-}

module Dict.Tests where

import Algebra.Heyting
import Algebra.Lattice
import Dict.Algebra
import PrettyShow
import Test.QuickCheck hiding ((><))
import Test.Tasty (TestTree, testGroup)

-- import Test.Tasty.HUnit (Assertion, assertBool, assertFailure, testCase, (@?=))

import Test.Tasty.HUnit (testCase, (@?=))
import Test.Tasty.QuickCheck (testProperty)

---------------------------------------------------
-- Generation of relations
---------------------------------------------------
checkEq :: Relation -> Relation -> Property
checkEq lhs rhs =
  counterexample
    ( "Pretty:\nLHS: "
        ++ pshow lhs
        ++ "\nRHS: "
        ++ pshow rhs
        ++ "\nNormal:\nLHS: "
        ++ show lhs
        ++ "\nRHS: "
        ++ show rhs
    )
    $ property (lhs `dictEq` rhs)

genPair :: Gen (Relation, Relation)
genPair = do
  n <- chooseInt (0, 5)
  x <- genRel n
  y <- genRel n
  pure (x, y)

genTriple :: Gen (Relation, Relation, Relation)
genTriple = do
  n <- chooseInt (0, 5)
  x <- genRel n
  y <- genRel n
  z <- genRel n
  pure (x, y, z)

prop_eqSelf :: Relation -> Property
prop_eqSelf d = checkEq d d

prop_interComm :: Property
prop_interComm = forAll genPair $ \(x, y) -> checkEq (x /\ y) (y /\ x)

-- prop_normalizeEq :: Relation -> Property
-- prop_normalizeEq d = checkEq d (normalize d)

allEqual :: (Eq a) => [a] -> Bool
allEqual [] = True
allEqual (x : xs) = all (== x) xs

-- prop_depthConstant :: Relation -> Bool
-- prop_depthConstant d = allEqual $ depthsAll d

-- prop_prodAddDepths :: Relation -> Relation -> Property
-- prop_prodAddDepths x y = (depth x + depth y) === depth (x >< y)

-- prop_dimElemsWildEq :: Relation -> Bool
-- prop_dimElemsWildEq (R {branches = xs, wild = Bottom}) = IntMap.null xs
-- prop_dimElemsWildEq (R {wild = Lift w, branches = xs}) = all prop_dimElemsWildEq xs || prop_dimElemsWildEq w || allEqual ((depthsAll `concatMap` IntMap.elems xs) ++ (depthsAll w))

prop_noEmptyBranches :: Relation -> Bool
prop_noEmptyBranches r = isEmpty r || hasNoEmpty r

prop_noEmptyBranchesBin :: (Relation -> Relation -> Relation) -> Relation -> Relation -> Bool
prop_noEmptyBranchesBin f r s = prop_noEmptyBranches (r `f` s)

--- Complements
prop_20 :: Relation -> Property
prop_20 d = checkEq d $ (neg . neg) d

prop_21 :: Property
prop_21 = forAll genPair $ \(x, y) -> counterexample (pshow x ++ "\n" ++ pshow y ++ "\n") $ checkEq (neg (x /\ y)) (neg x \/ neg y)

propertyTests :: TestTree
propertyTests =
  testGroup
    "Dict property-tests"
    [ testProperty "eqSelf" prop_eqSelf
    , -- , testProperty "constant depth" prop_depthConstant
      testProperty "intersect commutative" prop_interComm
    , testProperty "(20) Double complement" prop_20
    , testProperty "(21)" prop_21
    , -- , testProperty "normalize does nothing" prop_normalizeEq
      -- , testProperty "Prod adds depths" prop_prodAddDepths
      -- , testProperty "Dim of elems and wild match" prop_dimElemsWildEq
      testProperty "No empty plain" prop_noEmptyBranches
    , testProperty "No empty neg" (prop_noEmptyBranches . neg)
    , testProperty "No empty inter" (prop_noEmptyBranchesBin (/\))
    , testProperty "No empty union" (prop_noEmptyBranchesBin (\/))
    , testProperty "No empty diff" (prop_noEmptyBranchesBin (\\))
    , testProperty "No empty sym" (prop_noEmptyBranchesBin sym)
    -- , testProperty "No empty union" (prop_noEmptyBranchesUnion)
    -- , testProperty "No empty diff" (prop_noEmptyBranchesDiff)
    -- , testProperty "No empty sym" (prop_noEmptyBranchesSym)
    ]

fin :: [Int] -> Relation
fin = finite

cfin :: [Int] -> Relation
cfin = cofinite

simpleTests :: TestTree
simpleTests =
  testGroup
    "Simple Dict tests"
    [ testCase "inter 1" $ fin [1, 2, 3] /\ fin [2, 3, 4] @?= fin [2, 3]
    , testCase "inter 2" $ cfin [1, 2, 3] /\ cfin [2, 3, 4] @?= cfin [1, 2, 3, 4]
    , testCase "inter 3" $ fin [1, 2, 3] /\ cfin [2, 3, 4] @?= fin [1]
    , testCase "inter 4" $ cfin [1, 2, 3] /\ fin [2, 3, 4] @?= fin [4]
    , testCase "union 1" $ fin [1, 2, 3] \/ fin [2, 3, 4] @?= fin [1, 2, 3, 4]
    , testCase "union 2" $ cfin [1, 2, 3] \/ cfin [2, 3, 4] @?= cfin [2, 3]
    , testCase "union 3" $ fin [1, 2, 3] \/ cfin [2, 3, 4] @?= cfin [4]
    , testCase "union 4" $ cfin [1, 2, 3] \/ fin [2, 3, 4] @?= cfin [1]
    ]

tests :: TestTree
tests =
  testGroup
    "All dict tests"
    [ -- propertyTests,
      simpleTests
    ]
