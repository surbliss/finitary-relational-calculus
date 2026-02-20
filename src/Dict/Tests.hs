module Dict.Tests where

import Data.IntMap qualified as Map
import Data.Maybe (isJust)
import Dict.Algebra
import GHC.TypeLits
import Test.QuickCheck hiding ((><))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, assertFailure, testCase, (@?=))
import Test.Tasty.QuickCheck (testProperty)

---------------------------------------------------
-- Generation of relations
---------------------------------------------------
instance Arbitrary Dict where
  arbitrary = genDict
  shrink = shrinkDict

shrinkDict :: Dict -> [Dict]
shrinkDict End = []
shrinkDict (Dict Nothing d) =
  [End]
    ++ Map.elems d
    ++ [Dict Nothing (Map.delete x d) | x <- Map.keys d]
    ++ [Dict Nothing (Map.delete x d) | x <- Map.keys d]
shrinkDict (Dict (Just w) d) =
  shrinkDict (Dict Nothing d)
    ++ [Dict (Just x) d | x <- shrinkDict w]

genKey :: Gen Key
genKey = arbitrary

genDictDepth :: Int -> Gen Dict
genDictDepth n | n < 1 = pure End
genDictDepth n = do
  nKeys <- chooseInt (1, 5)
  keys <- vectorOf nKeys genKey
  ds <- vectorOf nKeys (frequency [(2, genDictDepth (n - 1)), (1, pure End)])
  w <- genWild (genDictDepth (n - 1))
  pure $ fromList w (zip keys ds)

genWild :: Gen Dict -> Gen Wilds
genWild gd = frequency [(1, Just <$> gd), (2, pure Nothing)]

genDict :: Gen Dict
genDict = do
  n <- chooseInt (0, 5)
  genDictDepth n

prop_eqSelf :: Dict -> Property
prop_eqSelf d = checkEq d d

binUnaryProp :: (Dict -> Dict) -> (Dict -> Dict) -> Property
binUnaryProp f g = forAll genDict $ \x ->
  let lhs = f x
      rhs = g x
   in counterexample ("LHS: " ++ show lhs ++ "\nRHS: " ++ show rhs) $
        property (lhs `dictEq` rhs)

binDictProp :: (Dict -> Dict -> Dict) -> (Dict -> Dict -> Dict) -> Property
binDictProp f g = forAll genDict $ \x -> forAll genDict $ \y ->
  let lhs = f x y
      rhs = g x y
   in counterexample ("LHS: " ++ show lhs ++ "\nRHS: " ++ show rhs) $
        property (lhs `dictEq` rhs)

--- Complements
checkEq :: Dict -> Dict -> Property
checkEq lhs rhs =
  counterexample ("LHS: " ++ show lhs ++ "\nRHS: " ++ show rhs) $
    property (lhs `dictEq` rhs)

prop_20 :: Dict -> Property
prop_20 d = checkEq d $ compl (compl d)

tests :: TestTree
tests =
  testGroup
    "Dict tests"
    [ testCase "Test-test" $ assertBool "Test-test" True
    , testProperty "eqSelf" prop_eqSelf
    , testProperty "(20) Double complement" prop_20
    ]
