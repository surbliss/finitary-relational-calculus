module Dict.Tests (tests) where

import Dict.Algebra
import Test.QuickCheck hiding ((><))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import Test.Tasty.QuickCheck (testProperty)

---------------------------------------------------
-- Generation of relations
---------------------------------------------------
prop_eqSelf :: Relation1 -> Property
prop_eqSelf (Rel1 d) = d === d

prop_pairSameDim :: Relation2 -> Property
prop_pairSameDim (Rel2 (x, y)) = dim x === dim y

prop_tripleSameDim :: Relation3 -> Property
prop_tripleSameDim (Rel3 (x, y, z)) = dim x === dim y .&&. dim y == dim z

prop_interComm :: Relation2 -> Property
prop_interComm (Rel2 (x, y)) = (x /\ y) === (y /\ x)

prop_noEmptyBranches :: Relation1 -> Bool
prop_noEmptyBranches (Rel1 r) = isEmptyRelation r || (not . hasEmpty) r

prop_noEmptyBranchesBin :: (Relation -> Relation -> Relation) -> Relation2 -> Bool
prop_noEmptyBranchesBin f (Rel2 (r, s)) = prop_noEmptyBranches (Rel1 $ r `f` s)

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
prop_20 :: Relation1 -> Property
prop_20 (Rel1 d) = d === neg (neg d)

prop_21 :: Relation2 -> Property
prop_21 (Rel2 (x, y)) = neg (x /\ y) === neg x \/ neg y

prop_22 :: Relation1 -> Relation1 -> Property
prop_22 (Rel1 x) (Rel1 y) = neg (x >< y) === ((neg x >< univRelN (dim y)) \/ (univRelN (dim x) >< neg y))

prop_23 :: Relation2 -> Property
prop_23 (Rel2 (x, y)) = neg (x \/ y) === neg x /\ neg y

prop_24 :: Relation1 -> Property
prop_24 (Rel1 x) = (x /\ emptyRelN (dim x)) === emptyRelN (dim x)

prop_25 :: Relation1 -> Property
prop_25 (Rel1 x) = (emptyRelN (dim x)) /\ x === emptyRelN (dim x)

prop_26 :: Relation1 -> Property
prop_26 (Rel1 x) = x /\ univRelN (dim x) === x

prop_27 :: Relation1 -> Property
prop_27 (Rel1 x) = (univRelN (dim x) /\ x) === x

prop_28 :: Relation3 -> Property
prop_28 (Rel3 (x, y, z)) = (x /\ (y \/ z)) === ((x /\ y) \/ (x /\ z))

prop_29 :: Relation3 -> Property
prop_29 (Rel3 (x, y, z)) = ((x \/ y) /\ z) === ((x /\ z) \/ (y /\ z))

--- Also: For these, they don't all need to be same dim, so consider writing some new product-specific ones.
prop_30 :: Relation2 -> Relation2 -> Property
prop_30 (Rel2 (c, e)) (Rel2 (d, f)) = (c >< d) /\ (e >< f) === (c /\ e) >< (d /\ f)

prop_31 :: Relation1 -> Relation2 -> Property
prop_31 (Rel1 c) (Rel2 (d, e)) = c >< (d \/ e) === (c >< d) \/ (c >< e)

prop_32 :: Relation2 -> Relation1 -> Property
prop_32 (Rel2 (c, d)) (Rel1 e) = (c \/ d) >< e === (c >< e) \/ (d >< e)

prop_symNilpotent :: Relation1 -> Property
prop_symNilpotent (Rel1 x) = x <+> x === emptyRelN (dim x)

prop_symComm :: Relation2 -> Property
prop_symComm (Rel2 (x, y)) = x <+> y === y <+> x
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
    , testProperty "No empty neg" (prop_noEmptyBranches . \(Rel1 x) -> Rel1 (neg x))
    , testProperty "No empty inter" (prop_noEmptyBranchesBin (/\))
    , testProperty "No empty union" (prop_noEmptyBranchesBin (\/))
    , testProperty "No empty diff" (prop_noEmptyBranchesBin (\\))
    , testProperty "No empty sym" (prop_noEmptyBranchesBin (<+>)) --
    --- Dimensions
    , testProperty "Pair same dim" $ prop_pairSameDim
    , testProperty "Triple same dim" $ prop_tripleSameDim --
    , testProperty "<+> nilpotent" $ prop_symNilpotent --
    , testProperty "<+> commutative" $ prop_symComm --
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
