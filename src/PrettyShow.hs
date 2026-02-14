module PrettyShow where

import Data.List (intercalate)
import Data.Set (Set)
import Data.Set qualified as Set

class PrettyShow a where
  pshow :: a -> String

instance PrettyShow String where
  pshow xs = xs

instance PrettyShow Int where
  pshow xs = show xs

instance (PrettyShow a) => PrettyShow (Set a) where
  pshow xs = "{" ++ intercalate ", " (map pshow (Set.elems xs)) ++ "}"

pprint :: (PrettyShow a) => a -> IO ()
pprint = putStrLn . pshow

withOp :: (PrettyShow a) => String -> [a] -> String
withOp op xs = intercalate op (map pshow xs)

withParens :: String -> String
withParens s = "(" ++ s ++ ")"
