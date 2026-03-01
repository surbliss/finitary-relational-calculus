-- TODO: Find better solution than removing this warning...
{-# OPTIONS_GHC -Wno-orphans #-}

module Dict.Tests where

import Algebra.Heyting
import Algebra.Lattice
import Algebra.Lattice.Dropped
import Algebra.Lattice.Lifted
import Data.IntMap qualified as IntMap
import Dict.Algebra
import PrettyShow
import Test.QuickCheck hiding ((><))
import Test.Tasty (TestTree, testGroup)

-- import Test.Tasty.HUnit (Assertion, assertBool, assertFailure, testCase, (@?=))
import Test.Tasty.QuickCheck (testProperty)

---------------------------------------------------

-- Remove all empty dead-ends
maybeNormal :: Relation -> Maybe Relation
maybeNormal r@R {branches = Top} = Just r
maybeNormal R {branches = Drop xs} | null xs = Nothing
maybeNormal r@R {branches = Drop xs} = Just $ r {branches = Drop (IntMap.map normalize xs)}

normalizeMaybe :: Relation -> Maybe Relation
normalizeMaybe R {branches = Drop xs, wild = Bottom} | IntMap.null xs = Nothing
normalizeMaybe r = case (newWild, newBranches) of
  (Bottom, Drop xs) | IntMap.null xs -> Nothing
  _ -> Just r {wild = newWild, branches = newBranches}
  where
    newWild = case wild r of
      Bottom -> Bottom
      Lift w -> case normalizeMaybe w of
        Nothing -> Bottom
        Just w' -> Lift w'
    newBranches = case branches r of
      Top -> Top
      Drop xs -> Drop $ IntMap.mapMaybe normalizeMaybe xs

-- normalizeMaybe r@R {branches = Top, wild = Bottom} = Just r
-- normalizeMaybe r@R {branches = Top, wild = Lift w} = case normalizeMaybe w of
--   Just w' -> Just r {wild = Lift w'}
--   Nothing -> Just r {wild = bottom}

normalize :: Relation -> Relation
normalize r = case normalizeMaybe r of
  Just x -> x
  Nothing -> bottom

-- delFirstBranches :: Branches -> Branches
-- delFirstBranches Top = Top
-- delFirstBranches  (Drop xs) = Drop $  xs

-- delFirst :: Relation -> Relation
-- delFirst r

projLast :: Relation -> Relation
projLast R {branches = Drop xs, wild = Bottom} | IntMap.null xs = bottom
projLast R {dim = 1} = top
projLast r@R {branches = Top} = r
projLast r@R {branches = Drop xs, wild = Lift w, dim = n} = r {branches = Drop $ IntMap.map projLast xs, wild = Lift $ projLast w, dim = n - 1}
projLast r@R {branches = Drop xs, wild = Bottom, dim = n} = r {branches = Drop $ IntMap.map projLast xs, dim = n - 1}

-- normalize r = case (properRel r, wild r) of
--   (Nothing, _) -> r {branches = undefined}
--   Just x -> x {branches = normalize branches x}

-- normalize r@R{branches=Top, wild = Bottom} = r
-- normalize Bottom = Bottom
-- normalize (R (xs, Univ)) = R (IntMap.map normalize xs, Univ)
-- normalize (R (xs, W ys)) = case (IntMap.map normalize xs, normalize ys) of
--   (xs', Univ) -> undefined

-- Generator + arbitrary
arbitraryRelIntMap :: Gen (IntMap (Relation))
arbitraryRelIntMap = do
  n <- chooseInt (0, 5)
  genRelIntMap n

--- Don't shrink into empties!
shrinkRelMap :: IntMap (Relation) -> [IntMap (Relation)]
shrinkRelMap xs = deletedKeys ++ shrunkElems
  where
    -- NOTE: Can also produce empty mapping
    deletedKeys = [IntMap.delete x xs | x <- IntMap.keys xs]
    shrunkElems =
      [ IntMap.insert x ys' xs
      | (x, ys) <- IntMap.assocs xs
      , ys' <- shrink ys
      -- , not (isEmpty ys') -- _But_ never allow binding a key to an empty map!
      ]

instance Arbitrary (Relation) where
  arbitrary = do
    n <- chooseInt (0, 5)
    genRel n

  shrink r =
    [r {branches = xs} | xs <- shrinkBranches (branches r)]
      <> [r {wild = w} | w <- shrinkWild (wild r)]
      <> [projLast r]
      <> [s | Drop xs <- [branches r], s <- IntMap.elems xs]
      <> [w | Lift w <- [wild r]]

-- shrink (R Bottom (xs)) = [R bottom (xs') | xs' <- shrinkRelMap xs]
-- shrink (R (Lift ys) (xs)) =
--   [R (Lift ys) (xs') | xs' <- shrinkRelMap xs]
--     ++ [R (Lift ys') (xs) | ys' <- shrink ys]
--     ++ [R bottom (xs)]
--     ++ shrinkElems (R (Lift ys) xs)
--     ++ shrinkWild (R (Lift ys) xs)

-- ++ [projLast (R (Lift ys) (xs))]

-- projElems :: (Relation) -> (Relation)
-- projElems Univ = Univ
-- projElems (R _ xs) | all (== Univ) xs = Univ
-- projElems (R w xs) = R w $ projElems <$> xs

shrinkBranches :: Branches -> [Branches]
shrinkBranches Top = []
shrinkBranches (Drop xs) = [Top] ++ [Drop ys | ys <- shrink xs]

-- shrinkElems :: (Relation) -> [(Relation)]
-- shrinkElems r@R {branches = xs}
--   | null xs = []
--   | all (== Top) xs = [top]
--   | otherwise = r {branches = traverse shrinkElems xs}

shrinkWild :: Wild -> [Wild]
shrinkWild Bottom = []
shrinkWild (Lift w) =
  [Bottom]
    ++ [ Lift w'
       | w' <- shrink w
       , case branches w' of
           Drop xs -> not (IntMap.null xs)
           Top -> True
       , not (wild w' == Bottom)
       ]

-- shrinkWild :: (Relation) -> [(Relation)]
-- shrinkWild R {wild = Bottom} = []
-- shrinkWild R {wild = Lift (R {branches = Top})} = [top]
-- shrinkWild r = [r {wild = Lift w'} | w' <- shrinkWild (wild r)]

genRel :: Int -> Gen (Relation)
genRel n | n < 1 = pure top
genRel n = do
  nKeys <- chooseInt (1, 5)
  keys <- vectorOf nKeys (arbitrary :: Gen Key)
  ds <- vectorOf nKeys $ genRel (n - 1)
  w <- genWild (n - 1)
  pure $ R {wild = w, branches = Drop (IntMap.fromList (zip keys ds)), dim = fromIntegral n}

genWild :: Int -> Gen Wild
genWild n | n < 0 = pure Bottom
genWild n = Lift <$> genRel n

genRelIntMap :: Int -> Gen (IntMap (Relation))
genRelIntMap n | n < 1 = pure IntMap.empty
genRelIntMap n = do
  nKeys <- chooseInt (1, 5)
  keys <- vectorOf nKeys arbitrary
  vals <- vectorOf nKeys (frequency [(2, genRel (n - 1)), (1, pure top)])
  pure $ fromList (zip keys vals)

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

-- prop_depthConstant :: Relation -> Bool
-- prop_depthConstant d = allEqual $ depthsAll d

-- prop_prodAddDepths :: Relation -> Relation -> Property
-- prop_prodAddDepths x y = (depth x + depth y) === depth (x >< y)

-- prop_dimElemsWildEq :: Relation -> Bool
-- prop_dimElemsWildEq (R {branches = xs, wild = Bottom}) = IntMap.null xs
-- prop_dimElemsWildEq (R {wild = Lift w, branches = xs}) = all prop_dimElemsWildEq xs || prop_dimElemsWildEq w || allEqual ((depthsAll `concatMap` IntMap.elems xs) ++ (depthsAll w))

--- Complements
prop_20 :: Relation -> Property
prop_20 d = checkEq d $ (neg . neg) d

prop_21 :: Property
prop_21 = forAll genPair $ \(x, y) -> counterexample (pshow x ++ "\n" ++ pshow y ++ "\n") $ checkEq (neg (x /\ y)) (neg x \/ neg y)

tests :: TestTree
tests =
  testGroup
    "Dict tests"
    [ testProperty "eqSelf" prop_eqSelf
    , -- , testProperty "constant depth" prop_depthConstant
      testProperty "intersect commutative" prop_interComm
    , testProperty "(20) Double complement" prop_20
    , testProperty "(21)" prop_21
    , testProperty "normalize does nothing" prop_normalizeEq
    -- , testProperty "Prod adds depths" prop_prodAddDepths
    -- , testProperty "Dim of elems and wild match" prop_dimElemsWildEq
    ]
