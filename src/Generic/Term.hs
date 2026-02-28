{-# LANGUAGE GHC2024 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Generic.Term (
  Term,
  finite,
  cofinite,
  empty1,
  univ,
  complement,
  (/\),
  (\/),
  (><),
  -- perm,
  proj,
  diag,
  -- join,
  eval,
  pprint,
)
where

import Generic.Algebra qualified as A
import Generic.Eval (Result)
import Generic.Eval qualified as E

import GHC.TypeLits

---------------------------------------------------
-- Datatypes
---------------------------------------------------
-- Wrapper with dimension-info, i.e. length of Products
newtype Term (n :: Nat) a = Term (A.Union a) deriving (Eq, Show, Functor)

---------------------------------------------------
-- Exported constructors
---------------------------------------------------
finite :: (Ord a) => a -> Term 1 a
finite x = Term $ A.single $ A.Finite x

cofinite :: (Ord a) => a -> Term 1 a
cofinite x = Term $ A.single $ A.Cofinite x

-- Need to specify dimension manually
empty1 :: Term (n + 1) a
empty1 = Term A.empty1

-- Always dim 1, for higher dim do univ >< univ >< ...
univ :: (Ord a) => Term 1 a
univ = Term A.univ1

complement :: (Ord a) => Term n a -> Term n a
complement (Term x) = Term $ A.compl' x

--- Chose precedence to match the Term-structure:
infixl 6 \/
infixl 7 ><
infixl 8 /\

(/\) :: (Ord a) => Term n a -> Term n a -> Term n a
Term x /\ Term y = Term (x A./\ y)

(><) :: (Ord a) => Term n a -> Term m a -> Term (n + m) a
Term x >< Term y = Term (x A.>< y)

(\/) :: (Ord a) => Term n a -> Term n a -> Term n a
Term x \/ Term y = Term (x A.\/ y)

-- TODO: Permutation, projection and diagonalization
-- perm :: [Int] -> Term n a -> Term n a
-- perm is (Term x) = Term $ A.perm is x

-- If result is type Term 0 a, then it should always be the empty set
-- Also remember to rerun \/, so terms can be normalized
proj :: (Ord a) => Int -> Term (n + 2) a -> Term (n + 1) a
proj i (Term x) = Term $ A.proj i x

diag :: (Ord a) => Term (n + 2) a -> Term (n + 1) a
diag (Term x) = Term $ A.diag x

--
-- join :: Int -> Term n a -> Term n a -> Term (n + 1) a
-- join = undefined

pprint :: (A.PrettyShow a) => Term n a -> IO ()
pprint (Term x) = A.pprint x

--- Evaluation
eval :: (Ord a) => Term n a -> Maybe (Result a)
eval (Term x) = E.eval x
