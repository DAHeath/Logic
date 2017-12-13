module Logic.ImplicationGraph.LTree where

import Data.Data (Data)

data LTree a
  = Leaf a
  | LOnly (LTree a)
  | ROnly (LTree a)
  | Branch (LTree a) (LTree a)
  deriving (Show, Read, Eq, Ord, Data, Functor, Foldable, Traversable)

data Tag = L | R
  deriving (Show, Read, Eq, Ord, Data)

taggings :: LTree a -> [[Tag]]
taggings (Leaf _)   = [[]]
taggings (LOnly t)  = map (L:) (taggings t)
taggings (ROnly t)  = map (R:) (taggings t)
taggings (Branch lt rt) = map (L:) (taggings lt) ++ map (R:) (taggings rt)

noBr :: LTree a -> [LTree a]
noBr (Leaf a)   = [Leaf a]
noBr (LOnly t)  = map LOnly (noBr t)
noBr (ROnly t)  = map ROnly (noBr t)
noBr (Branch lt rt) = map LOnly (noBr lt) ++ map ROnly (noBr rt)

point :: LTree a -> a
point (Leaf a) = a
point (LOnly t) = point t
point (ROnly t) = point t
point _ = error "point of ltree with branch"

unionWith :: (a -> a -> a) -> LTree a -> LTree a -> LTree a
unionWith f (Leaf a) (Leaf b) = Leaf (f a b)
unionWith _ (Leaf a) _ = Leaf a
unionWith _ _ (Leaf b) = Leaf b
unionWith f (LOnly a) (LOnly b) = LOnly (unionWith f a b)
unionWith f (ROnly a) (ROnly b) = ROnly (unionWith f a b)
unionWith _ (LOnly a) (ROnly b) = Branch a b
unionWith _ (ROnly a) (LOnly b) = Branch b a
unionWith f (Branch a b) (LOnly c) = Branch (unionWith f a c) b
unionWith f (Branch a b) (ROnly c) = Branch a (unionWith f b c)
unionWith f (LOnly a) (Branch b c) = Branch (unionWith f a b) c
unionWith f (ROnly a) (Branch b c) = Branch b (unionWith f a c)
unionWith f (Branch a b) (Branch c d) = Branch (unionWith f a b) (unionWith f c d)
