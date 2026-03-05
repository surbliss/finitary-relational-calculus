module Dict.Tests (tests) where

import Algebra.Heyting
import Algebra.Lattice
import Dict.Algebra
import Test.QuickCheck hiding ((><))
import Test.Tasty (TestTree, testGroup)

-- import Test.Tasty.HUnit (Assertion, assertBool, assertFailure, testCase, (@?=))

import Test.Tasty.HUnit (testCase, (@?=))
import Test.Tasty.QuickCheck (testProperty)

---------------------------------------------------
-- Generation of relations
---------------------------------------------------
detailedEq :: Relation -> Relation -> Property
detailedEq lhs rhs =
  counterexample
    ( show (branches lhs)
        ++ show (wild lhs)
        ++ show (depth lhs)
        ++ "\n"
        ++ show (branches rhs)
        ++ show (wild rhs)
        ++ show (depth rhs)
    )
    $ property
    $ lhs `eq` rhs

prop_genSimplified :: Relation -> Property
prop_genSimplified r = r === simplify r

prop_eqSelf :: Relation -> Property
prop_eqSelf d = d === d

prop_pairSameDim :: Relation2 -> Property
prop_pairSameDim (Rel2 (x, y)) = depth x === depth y

prop_tripleSameDim :: Relation3 -> Property
prop_tripleSameDim (Rel3 (x, y, z)) = depth x === depth y .&&. depth y == depth z

prop_interComm :: Relation2 -> Property
prop_interComm (Rel2 (x, y)) = (x /\ y) `detailedEq` (y /\ x)

prop_noEmptyBranches :: Relation -> Bool
prop_noEmptyBranches r = isEmpty r || hasNoEmpty r

prop_noEmptyBranchesBin :: (Relation -> Relation -> Relation) -> Relation -> Relation -> Bool
prop_noEmptyBranchesBin f r s = prop_noEmptyBranches (r `f` s)

--- 1-dim rules, but should also hold in multi-dim:
prop_13 :: Relation2 -> Property
prop_13 (Rel2 (x, y)) = (x \/ neg y) === neg (y \\ x)
prop_14 :: Relation2 -> Property
prop_14 (Rel2 (x, y)) = (neg x \/ y) === neg (x \\ y)
prop_15 :: Relation2 -> Property
prop_15 (Rel2 (x, y)) = (neg x \/ neg y) === neg (x /\ y)
prop_16 :: Relation2 -> Property
prop_16 (Rel2 (x, y)) = (x /\ neg y) === x \\ y
prop_17 :: Relation2 -> Property
prop_17 (Rel2 (x, y)) = (neg x /\ y) === y \\ x
prop_18 :: Relation2 -> Property
prop_18 (Rel2 (x, y)) = (neg x /\ neg y) === neg (x \/ y)

-- Prop 19 is same as prop 20
--- Complements
prop_20 :: Relation -> Property
prop_20 d = d === neg (neg d)

prop_21 :: Relation2 -> Property
prop_21 (Rel2 (x, y)) = neg (x /\ y) === neg x \/ neg y

prop_22 :: Relation -> Relation -> Property
prop_22 x y = neg (x >< y) === ((neg x >< univN (depth y)) \/ (univN (depth x) >< neg y))

prop_23 :: Relation2 -> Property
prop_23 (Rel2 (x, y)) = neg (x \/ y) === neg x /\ neg y

prop_24 :: Relation -> Property
prop_24 x = (x /\ emptyN (depth x)) === emptyN (depth x)

prop_25 :: Relation -> Property
prop_25 x = (emptyN (depth x)) /\ x === emptyN (depth x)

prop_26 :: Relation -> Property
prop_26 x = x /\ univN (depth x) === x

prop_27 :: Relation -> Property
prop_27 x = (univN (depth x) /\ x) === x

prop_28 :: Relation3 -> Property
prop_28 (Rel3 (x, y, z)) = (x /\ (y \/ z)) === ((x /\ y) \/ (x /\ z))

-- prop_30
-- prop_31
-- prop_32

--- Couterexample:
-- (28):                   FAIL (0.04s)
--      *** Failed! Falsified (after 9 tests and 15 shrinks):
--      Rel3 ({5},{, * -> {, * -> {7}}},{, * -> {8 -> {-7, 7}}})
--      {5 -> {8 -> {-7}, * -> {7}}} /= {5 -> {8 -> {-7, 7}}}
--      Use --quickcheck-replay="(SMGen 6982499325617234579 14420437858484944245,8)" to reproduce.
--      Use -p '/(28)/' to rerun this test only.
--    (29):                   FAIL (0.07s)
--      *** Failed! Falsified (after 2 tests and 21 shrinks):
--      Rel3 ({, * -> {-1}},{1},{, * -> {, * -> {1}}})
--      {1 -> {-1 -> {1}, * -> {1}}, * -> {-1 -> {1}}} /= {, * -> {-1 -> {1}}}
--      Use --quickcheck-replay="(SMGen 6134009087970008456 4260353227498352113,1)" to reproduce.
--      Use -p '/(29)/' to rerun this test only.

prop_29 :: Relation3 -> Property
prop_29 (Rel3 (x, y, z)) = ((x \/ y) /\ z) === ((x /\ z) \/ (y /\ z))

time :: (Testable prop) => Int -> prop -> Property
time k = within $ k * 1000000

--- Also: For these, they don't all need to be same dim, so consider writing some new product-specific ones.
prop_30 :: Relation2 -> Relation2 -> Property
prop_30 (Rel2 (c, e)) (Rel2 (d, f)) = time 1 $ (c >< d) /\ (e >< f) === (c /\ e) >< (d /\ f)

prop_31 :: Relation -> Relation2 -> Property
prop_31 c (Rel2 (d, e)) = withMaxSuccess 100 $ time 1 $ c >< (d \/ e) === (c >< d) \/ (c >< e)

prop_32 :: Relation2 -> Relation -> Property
prop_32 (Rel2 (c, d)) e = withMaxSuccess 100 $ time 1 $ (c \/ d) >< e === (c >< e) \/ (d >< e)

propertyTests :: TestTree
propertyTests =
  testGroup
    "Dict property-tests"
    [ testProperty "eqSelf" prop_eqSelf
    , testProperty "intersect commutative" prop_interComm
    , testProperty "(13)" prop_13
    , testProperty "(14)" prop_14
    , testProperty "(15)" prop_15
    , testProperty "(16)" prop_16
    , testProperty "(17)" prop_17
    , testProperty "(18)" prop_18
    , testProperty "(20) Double complement" prop_20
    , testProperty "(21)" prop_21
    , testProperty "(22)" prop_22
    , testProperty "(23)" prop_23
    , testProperty "(24)" prop_24
    , testProperty "(25)" prop_25
    , testProperty "(26)" prop_26
    , testProperty "(27)" prop_27
    , testProperty "(28)" prop_28
    , testProperty "(29)" prop_29
    , testProperty "(30)" prop_30
    , testProperty "(31)" prop_31
    , testProperty "(32)" prop_32
    , testProperty "No empty plain" prop_noEmptyBranches
    , testProperty "No empty neg" (prop_noEmptyBranches . neg)
    , testProperty "No empty inter" (prop_noEmptyBranchesBin (/\))
    , testProperty "No empty union" (prop_noEmptyBranchesBin (\/))
    , testProperty "No empty diff" (prop_noEmptyBranchesBin (\\))
    , testProperty "No empty sym" (prop_noEmptyBranchesBin sym) --
    --- Dimensions
    , testProperty "Pair same dim" $ prop_pairSameDim
    , testProperty "Triple same dim" $ prop_tripleSameDim --
    --- Generators
    , testProperty "Gens simplified" $ prop_genSimplified
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
    [ propertyTests
    , simpleTests
    ]
