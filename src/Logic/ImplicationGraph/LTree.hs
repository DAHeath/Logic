{-# LANGUAGE DeriveDataTypeable, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Logic.ImplicationGraph.LTree where

import Data.Data (Data)

data LTree a
  = Leaf a
  | LOnly (LTree a)
  | ROnly (LTree a)
  | Br (LTree a) (LTree a)
  deriving (Show, Read, Eq, Ord, Data, Functor, Foldable, Traversable)

data Tag = L | R
  deriving (Show, Read, Eq, Ord, Data)

taggings :: LTree a -> [[Tag]]
taggings (Leaf a)   = [[]]
taggings (LOnly t)  = map (L:) (taggings t)
taggings (ROnly t)  = map (R:) (taggings t)
taggings (Br lt rt) = map (L:) (taggings lt) ++ map (R:) (taggings rt)

noBr :: LTree a -> [LTree a]
noBr (Leaf a)   = [Leaf a]
noBr (LOnly t)  = map LOnly (noBr t)
noBr (ROnly t)  = map ROnly (noBr t)
noBr (Br lt rt) = map LOnly (noBr lt) ++ map ROnly (noBr rt)

point :: LTree a -> a
point (Leaf a) = a
point (LOnly t) = point t
point (ROnly t) = point t
point t = error "point of ltree with branch"
