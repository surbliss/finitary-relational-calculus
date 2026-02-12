{-# LANGUAGE GHC2024 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module TermSet (
  Term,
  fins,
  cfins,
  finite,
  cofinite,
  empty,
  univ,
  complement,
  (/\),
  (\/),
  (><),
  proj,
  perm,
  diag,
  join,
  pprint,
)
where

import AlgebraSet qualified as A

-- import Eval (Result)
-- import Eval qualified as E

import GHC.TypeLits

---------------------------------------------------
-- Datatypes
---------------------------------------------------
-- Wrapper with dimension-info, i.e. length of Products
newtype Term (n :: Nat) a = Term (A.SetAlgebra a) deriving (Eq, Show)

---------------------------------------------------
-- Exported constructors
---------------------------------------------------
--- For repl-testing
fins :: [Int] -> Term 1 Int
fins = finite

cfins :: [Int] -> Term 1 Int
cfins = cofinite

finite :: (Ord a, Eq a) => [a] -> Term 1 a
finite xs = Term $ A.fins xs

cofinite :: (Ord a, Eq a) => [a] -> Term 1 a
cofinite x = Term $ A.compl $ A.fins x

-- Need to specify dimension manually
empty :: Term 1 a
empty = Term A.empty1

-- Always dim 1, for higher dim do univ >< univ >< ...
univ :: (Eq a) => Term 1 a
univ = Term A.univ1

complement :: (Ord a, Eq a) => Term n a -> Term n a
complement (Term x) = Term $ A.compl x

--- Chose precedence to match the Term-structure:
infixl 6 \/
infixl 7 ><
infixl 8 /\

(/\) :: (Ord a, Eq a) => Term n a -> Term n a -> Term n a
Term x /\ Term y = Term (x A./\ y)

(><) :: (Ord a, Eq a) => Term n a -> Term m a -> Term (n + m) a
Term x >< Term y = Term (x A.>< y)

(\/) :: (Ord a, Eq a) => Term n a -> Term n a -> Term n a
Term x \/ Term y = Term (x A.\/ y)

-- TODO: Permutation, projection and diagonalization
perm :: [Int] -> Term n a -> Term n a
perm = undefined

-- If result is type Term 0 a, then it should always be the empty set
-- Also remember to rerun \/, so terms can be normalized
proj :: (Eq a) => Int -> Term (n + 2) a -> Term (n + 1) a
proj = undefined

diag :: (Eq a) => Term (n + 2) a -> Term (n + 1) a
diag = undefined

--
join :: Int -> Term n a -> Term n a -> Term (n + 1) a
join = undefined

pprint :: (A.PrettyShow a) => Term n a -> IO ()
pprint (Term x) = A.pprint x

--- Evaluation
-- eval :: (Ord a) => Term n a -> Maybe (Result a)
-- eval (Term x) = E.eval x
