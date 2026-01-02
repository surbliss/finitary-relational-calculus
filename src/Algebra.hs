{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Algebra
where

-- (FOL(..), Algebra (Empty, Univ), set, compl, (/\), (\/), (><), term)

import GHC.TypeLits

---------------------------------------------------
-- Datatypes
---------------------------------------------------

-- Check if valid at evaluation, maybe by holding a dimension parameter?
data Algebra a where
  Finite :: a -> Algebra a
  Empty :: Algebra a
  C :: Algebra a -> Algebra a
  -- Intersections only allowed in each factor of product
  (:/\) :: Algebra a -> Algebra a -> Algebra a -- Intersection
  (:\/) :: Algebra a -> Algebra a -> Algebra a -- Union
  (:><) :: Algebra a -> Algebra a -> Algebra a -- Cross product

-- Dimension 1 algebra, for writing as a tensor term
data SingleAlgebra a where
  SEmpty :: SingleAlgebra a
  SUniv :: SingleAlgebra a
  SFinite :: a -> SingleAlgebra a
  SCofinite :: a -> SingleAlgebra a
  (::/\) :: SingleAlgebra a -> SingleAlgebra a -> SingleAlgebra a

-- (::\/) :: SingleAlgebra a -> SingleAlgebra a -> SingleAlgebra a

infixr 5 :\/

-- infixr 5 ::\/
infixr 6 :/\
infixr 6 ::/\
infixr 7 :><

deriving instance (Show a) => Show (Algebra a)
deriving instance (Show a) => Show (SingleAlgebra a)

pattern Cofinite :: a -> Algebra a
pattern Cofinite x = C (Finite x)

pattern Univ :: Algebra a
pattern Univ = C (Empty)

---------------------------------------------------
-- Exported constructors
---------------------------------------------------
set :: a -> Algebra a
set x = Finite x

-- Move all complements _in_ to the Finitary constructors
compl :: Algebra a -> Algebra a
compl (Finite x) = Cofinite x
compl (C x) = x
compl Empty = Univ
compl Univ = Empty
compl (x :/\ y) = compl x \/ compl y
compl (x :>< y) = (Univ >< compl y) \/ (compl x >< Univ)
compl (x :\/ y) = compl x /\ compl y

-- Move the unions up, and intersections down into 1-dim algebras
(\/) :: Algebra a -> Algebra a -> Algebra a
s \/ Empty = s
Empty \/ s = s
_ \/ Univ = Univ
Univ \/ _ = Univ
x \/ y = x :\/ y

(/\) :: Algebra a -> Algebra a -> Algebra a
-- Unit elements
_ /\ Empty = Empty
Empty /\ _ = Empty
s /\ Univ = s
Univ /\ s = s
-- Distribution into unions
-- see (28) to (30)
-- NOTE: This duplicates terms. So maybe better to defer this operation?
c /\ (d :\/ e) = (c /\ d) \/ (c /\ e)
(c :\/ d) /\ e = (c /\ e) \/ (d /\ e)
-- Distribution over cross product
-- WARN: This is wrong if dim c /= dim e or dim d/= f. More sophisticated checks should be added.
(c :>< d) /\ (e :>< f) = (c /\ e) >< (d /\ f)
x /\ y = x :/\ y

(><) :: Algebra a -> Algebra a -> Algebra a
-- Unit-cross products
Empty >< _ = Empty
_ >< Empty = Empty
x >< (y :\/ z) = (x >< y) \/ (x >< z)
(x :\/ y) >< z = (x >< z) \/ (y >< z)
x >< y = x :>< y

-- Union of products, all producs should be same size
term :: Algebra a -> [[SingleAlgebra a]]
term (a :\/ b) = term a ++ term b
term a = [prod a]
  where
    prod (x :>< y) = prod x ++ prod y
    prod x = [single x]
    single Empty = SEmpty
    single Univ = SUniv
    single (Finite x) = SFinite x
    single (Cofinite x) = SCofinite x
    single (x :/\ y) = single x ::/\ single y
    single (_ :\/ _) = error "oh no, union"
    single (_ :>< _) = error "oh no, product"
    single (C _) = error "oh no, complement"

---------------------------------------------------
-- Graveyard
---------------------------------------------------

-- Int?
type Permutation = [Nat]

data FOL (n :: Nat) a where
  -- Cross product of
  -- Predicate :: [Set a] -> FOL n a -- length list = n
  And :: FOL n a -> FOL n a -> FOL n a
  Or :: FOL n a -> FOL n a -> FOL n a
  Not :: FOL n a -> FOL n a
  Exists :: FOL n a -> FOL n a
  Extend :: FOL n a -> FOL n a
  Permute :: Permutation -> FOL n a -> FOL n a
  Mod :: FOL n a -> FOL n a

implies :: FOL n a -> FOL n a -> FOL n a
implies x y = (Not x) `And` y

forAll :: FOL n a -> FOL n a
forAll x = Not (Exists (Not x))
