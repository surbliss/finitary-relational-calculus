{-# LANGUAGE GHC2024 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Query (Query (..)) where

-- Finitary Query: Built from base (sets), unions, empty set (Ø), intersection, universal set (1), complement, product, permute, diagonal, projection.

data Query a where
  Base :: a -> Query a
  Empty :: Query a
  Univ :: Query a
  Complement :: Query a -> Query a
  (:/\) :: Query a -> Query a -> Query a
  (:\/) :: Query a -> Query a -> Query a
  (:><) :: Query a -> Query a -> Query  a


-- Permute :: [Int] -> Query n a -> Query n a
-- Diagonal :: Query n a -> Query (n + 1) a
-- Projection :: Query (n + 1) a -> Query n a
