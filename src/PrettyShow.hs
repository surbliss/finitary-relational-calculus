module PrettyShow where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.List (intercalate)
import Data.Set (Set, toList)

class PrettyShow a where
  pshow :: a -> String

instance PrettyShow String where
  pshow xs = xs

instance PrettyShow Int where
  pshow xs = show xs

instance (PrettyShow a) => PrettyShow (Set a) where
  pshow xs = "{" ++ intercalate ", " (map pshow (toList xs)) ++ "}"

instance (PrettyShow a) => PrettyShow (IntMap a) where
  pshow d = "{" ++ strs ++ "}"
    where
      strs = intercalate ", " $ do
        (k, v) <- IntMap.assocs d
        pure $ show k ++ " -> " ++ pshow v

instance PrettyShow IntSet where
  pshow xs = "{" ++ intercalate ", " (pshow <$> (IntSet.toList xs)) ++ "}"

instance (PrettyShow a) => PrettyShow [a] where
  pshow xs = "[" ++ intercalate ", " (map pshow xs) ++ "]"

pprint :: (PrettyShow a) => a -> IO ()
pprint = putStrLn . pshow

withOp :: (PrettyShow a) => String -> [a] -> String
withOp op xs = intercalate op (map pshow xs)

withParens :: String -> String
withParens s = "(" ++ s ++ ")"
