{-# LANGUAGE GHC2024 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Set.Term where

-- module Set.Term (
--   Term,
--   fins,
--   cfins,
--   fin,
--   cfin,
--   empty,
--   univ,
--   compl,
--   (/\),
--   (\/),
--   (><),
--   (\\),
--   proj,
--   perm,
--   diag,
--   join,
--   pprint,
-- )
-- where

import PrettyShow
import Set.Algebra qualified as A

-- import Eval (Result)
-- import Eval qualified as E

import GHC.TypeLits

---------------------------------------------------
-- Datatypes
---------------------------------------------------
-- Wrapper with dimension-info, i.e. length of Products
newtype Term (n :: Nat) = Term (A.Algebra) deriving (Eq, Show)

---------------------------------------------------
-- Exported constructors
---------------------------------------------------
--- For repl-testing
fins :: [Int] -> Term 1
fins xs = Term $ A.fins xs

cfins :: [Int] -> Term 1
cfins x = Term $ A.compl $ A.fins x

fin :: Int -> Term 1
fin x = fins [x]

cfin :: Int -> Term 1
cfin x = cfins [x]

-- Need to specify dimension manually
empty :: Term 1
empty = Term $ A.emptyA 1

-- Always dim 1, for higher dim do univ >< univ >< ...
univ :: Term 1
univ = Term $ A.univ 1

compl :: Term n -> Term n
compl (Term x) = Term $ A.complement x

--- Chose precedence to match the Term-structure:
infixl 6 \/
infixl 7 ><
infixl 8 /\

(/\) :: Term n -> Term n -> Term n
Term x /\ Term y = Term (x `A.inter` y)

(><) :: Term n -> Term m -> Term (n + m)
Term x >< Term y = Term (x `A.prod` y)

(\/) :: Term n -> Term n -> Term n
Term x \/ Term y = Term (x `A.union` y)

--- Term 1 is always base, so safe to take difference
(\\) :: Term 1 -> Term 1 -> Term 1
Term x \\ Term y = Term $ x A.\\ y

-- TODO: Permutation, projection and diagonalization
-- perm :: [Int] -> Term n -> Term n
-- perm = undefined

-- If result is type Term 0 , then it should always be the empty set
-- Also remember to rerun \/, so terms can be normalized
proj :: Int -> Term (n + 2) -> Term (n + 1)
proj i (Term x) = Term $ A.proj i x

-- diag :: Term (n + 2) -> Term (n + 1)
-- diag = undefined

--
-- join :: Int -> Term n -> Term n -> Term (n + 1)
-- join = undefined

--- Extras - aliases to easier read FOL queries
-- Implies
(-->) :: Term n -> Term n -> Term n
x --> y = compl x \/ y

exists :: Int -> Term (n + 2) -> Term (n + 1)
exists = proj

forAll :: Int -> Term (n + 2) -> Term (n + 1)
forAll i x = compl $ exists i $ compl x

instance PrettyShow (Term n) where
  pshow (Term x) = pshow x

--- Evaluation
-- eval ::  Term n  -> Maybe (Result a)
-- eval (Term x) = E.eval x
