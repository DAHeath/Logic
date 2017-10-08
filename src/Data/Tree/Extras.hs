module Data.Tree.Extras where

import qualified Data.Tree as T
import           Data.Tree (Tree)

zipTree :: (a -> b -> c) -> Tree a -> Tree b -> Tree c
zipTree f (T.Node a as) (T.Node b bs) = T.Node (f a b) (zipWith (zipTree f) as bs)
