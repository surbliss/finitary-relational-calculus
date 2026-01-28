{-# LANGUAGE GHC2024 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Term where

import Algebra qualified as A
import Eval (Result)
import Eval qualified as E

import GHC.TypeLits

---------------------------------------------------
-- Datatypes
---------------------------------------------------
-- Wrapper with dimension-info, i.e. length of Products
newtype Term (n :: Nat) a = Term (A.Union a) deriving (Eq, Show, Functor)

---------------------------------------------------
-- Exported constructors
---------------------------------------------------
finite :: a -> Term 1 a
finite x = Term $ A.single $ A.Finite x

cofinite :: a -> Term 1 a
cofinite x = Term $ A.single $ A.Cofinite x

-- Need to specify dimension manually
empty :: Term n a
empty = Term A.empty

-- Always dim 1, for higher dim do univ >< univ >< ...
univ :: Term 1 a
univ = Term A.univ1

complement :: Term n a -> Term n a
complement (Term x) = Term $ A.compl' x

(/\) :: Term n a -> Term n a -> Term n a
Term x /\ Term y = Term (x A./\ y)

(><) :: Term n a -> Term m a -> Term (n + m) a
Term x >< Term y = Term (x A.>< y)

(\/) :: Term n a -> Term n a -> Term n a
Term x \/ Term y = Term (x A.\/ y)

-- TODO: Permutation, projection and diagonalization
perm :: [Int] -> Term n a -> Term n a
perm is (Term x) = Term $ A.perm is x

-- If result is type Term 0 a, then it should always be the empty set
-- Also remember to rerun \/, so terms can be normalized
proj :: Term (n + 1) a -> Term n a
proj (Term x) = Term $ A.proj x

diag :: Term n a -> Term (n + 1) a
diag (Term x) = Term $ A.diag x

pprint :: (A.PrettyShow a) => Term n a -> IO ()
pprint (Term x) = A.pprint x

--- Evaluation
eval :: (Ord a) => Term n a -> Maybe (Result a)
eval (Term x) = E.eval x
