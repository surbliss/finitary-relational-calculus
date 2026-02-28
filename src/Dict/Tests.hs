module Dict.Tests where

import Algebra.Lattice
import Algebra.Lattice.Lifted
import Data.IntMap qualified as IntMap
import Dict.Algebra
import PrettyShow
import Test.QuickCheck hiding ((><))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, assertFailure, testCase, (@?=))
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

-- where
--   lhs = normalize x
--   rhs = normalize y

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

prop_normalizeEq :: Relation -> Property
prop_normalizeEq d = checkEq d (normalize d)

allEqual :: (Eq a) => [a] -> Bool
allEqual [] = True
allEqual (x : xs) = all (== x) xs

prop_depthConstant :: Relation -> Bool
prop_depthConstant d = allEqual $ depthsAll d

prop_prodAddDepths :: Relation -> Relation -> Property
prop_prodAddDepths x y = (depth x + depth y) === depth (x >< y)

prop_dimElemsWildEq :: Relation -> Bool
prop_dimElemsWildEq Univ = True
prop_dimElemsWildEq (R Bottom xs) = IntMap.null xs
prop_dimElemsWildEq (R (Lift w) xs) = all prop_dimElemsWildEq xs || prop_dimElemsWildEq w || allEqual ((depthsAll `concatMap` IntMap.elems xs) ++ (depthsAll w))

--- Complements
prop_20 :: Relation -> Property
prop_20 d = checkEq d $ (compl . compl) d

prop_21 :: Property
prop_21 = forAll genPair $ \(x, y) -> counterexample (pshow x ++ "\n" ++ pshow y ++ "\n") $ checkEq (compl (x /\ y)) (compl x \/ compl y)

tests :: TestTree
tests =
  testGroup
    "Dict tests"
    [ testProperty "eqSelf" prop_eqSelf
    , testProperty "constant depth" prop_depthConstant
    , testProperty "intersect commutative" prop_interComm
    , testProperty "(20) Double complement" prop_20
    , testProperty "(21)" prop_21
    , testProperty "normalize does nothing" prop_normalizeEq
    , testProperty "Prod adds depths" prop_prodAddDepths
    , testProperty "Dim of elems and wild match" prop_dimElemsWildEq
    ]
