{-# LANGUAGE FlexibleInstances #-}
module Logic.Name where

import           Control.Lens

import           Data.Typeable (Typeable)
import           Data.Data (Data)
import           Data.List (intercalate)
import           Data.List.Split (splitOn)

import           Text.Read (readMaybe)

class (Typeable a, Data a, Ord a, Show a) => Name a where
  name :: Prism' String a

instance Name Integer where
  name = _Show

instance Name String where
  name = id

instance Name [String] where
  name = prism' out inc
    where
      inc = Just . splitOn "/"
      out = intercalate "/"

data Located n = Located Integer n
  deriving (Show, Read, Eq, Ord, Data)

instance Name n => Name (Located n) where
  name = prism' out inc
    where
      inc s =
        let ws = splitOn "/" s
        in case ws of
          [] -> Nothing
          [_] -> Nothing
          (l : rest) -> do
            loc <- readMaybe (tail l)
            n <- intercalate "/" rest ^? name
            return (Located loc n)

      out (Located l n) =
        "v" ++ show l ++ "/" ++ name # n

data Aliasable n
  = Aliased n
  | NoAlias n
  deriving (Show, Read, Eq, Ord, Data)

instance Name n => Name (Aliasable n) where
  name = prism' out inc
    where
      inc s =
        case s of
          '#':rest -> Aliased <$> (rest ^? name)
          rest -> NoAlias <$> (rest ^? name)
      out (Aliased n) = '#' : name # n
      out (NoAlias n) = name # n
