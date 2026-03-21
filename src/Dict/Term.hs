{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Dict.Term (
  finite,
  cofinite,
  fin,
  cfin,
  empty,
  univ,
  neg,
  (/\),
  (<+>),
  (\/),
  (><),
  (\\),
  --- Testing
  dictdim,
  count,
  termdim,
  --- tmp
  exs,
)
where

import Data.Proxy (Proxy (..))
import Dict.Algebra qualified as A
import GHC.TypeLits (KnownNat, Nat, natVal, type (+))
import Test.QuickCheck hiding ((><))

import PrettyShow

---------------------------------------------------
-- Datatypes
---------------------------------------------------
newtype Term (n :: Nat) = Term (A.Relation) deriving (Eq, Show, Ord)

---------------------------------------------------
-- Exported constructors
---------------------------------------------------
finite :: [Int] -> Term 1
finite xs = Term (A.finite xs)

cofinite :: [Int] -> Term 1
cofinite xs = Term (A.cofinite xs)

fin :: Int -> Term 1
fin x = finite [x]

cfin :: Int -> Term 1
cfin x = cofinite [x]

--- Empty set
-- NOTE: Always 1-dimensional. To increase dimension, use, e.g. empty >< empty >< ...
empty :: Term 1
empty = Term $ A.empty

univ :: Term 1
univ = Term $ A.univRelN 1

--- Complement (NOT)
neg :: Term n -> Term n
neg (Term x) = Term (A.neg x)

infixl 6 \/
infixl 7 ><
infixl 8 /\

--- Instersection (AND)
(/\) :: Term n -> Term n -> Term n
Term x /\ Term y = Term (x A./\ y)

--- Symmetric difference (XOR)
(<+>) :: Term n -> Term n -> Term n
Term x <+> Term y = Term (x A.<+> y)

--- Union (OR)
(\/) :: Term n -> Term n -> Term n
Term x \/ Term y = Term (x A.\/ y)

--- Cartesian product
(><) :: Term n -> Term m -> Term (n + m)
Term x >< Term y = Term (x A.>< y)

--- Set difference
(\\) :: Term n -> Term n -> Term n
Term x \\ Term y = Term (x A.\\ y)

instance PrettyShow (Term n) where
  pshow (Term x) = pshow x

---------------------------------------------------
-- For testing
---------------------------------------------------
--- Dimension: Term n should _always_ have dim = n
dictdim :: Term n -> Int
dictdim (Term x) = A.dim x

--- Number of branches
count :: Term n -> Int
count (Term x) = A.countRel x

termdim :: forall n. (KnownNat n) => Term n -> Nat
termdim _ = fromIntegral (natVal (Proxy @n))

---------------------------------------------------
-- Not exported
--------------------------------------------------
--- Generator
instance (KnownNat n) => Arbitrary (Term n) where
  arbitrary = Term <$> A.genRelation (fromIntegral (natVal (Proxy @n)))

  shrink (Term x) = Term <$> A.shrinkRelSameDim x

--- tmp
exs :: forall n. (KnownNat n) => Proxy n -> IO ()
exs Proxy = do
  xs <- sample' (arbitrary :: Gen (Term n))
  mapM_ pprint xs
