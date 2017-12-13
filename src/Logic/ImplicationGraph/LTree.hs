module Logic.ImplicationGraph.LTree where

import           Data.Pointed
import           Data.Copointed
import           Data.Foldable (toList)
import           Data.Data (Data)
import           Data.Text.Prettyprint.Doc
import qualified Data.Map as M

import           Logic.ImplicationGraph.Types
import           Logic.Formula

data LTree a
  = Leaf a
  | LOnly (LTree a)
  | ROnly (LTree a)
  | Branch (LTree a) (LTree a)
  deriving (Show, Read, Eq, Ord, Data, Functor, Foldable, Traversable)

data Tag = L | R
  deriving (Show, Read, Eq, Ord, Data)

instance Pointed LTree where
  point = Leaf

instance Copointed LTree where
  copoint (Leaf a) = a
  copoint (LOnly a) = copoint a
  copoint (ROnly a) = copoint a
  copoint (Branch l _) = copoint l

instance Edge LTree where
  split (Leaf a)   = [Leaf a]
  split (LOnly t)  = map LOnly (split t)
  split (ROnly t)  = map ROnly (split t)
  split (Branch lt rt) = map LOnly (split lt) ++ map ROnly (split rt)

  collect is =
    let m = foldr (\i m' ->
          let ts = taggings i in
          foldr (\t -> M.insertWith (++) t (toList i)) m' ts) M.empty is
    in M.elems m
    where
      taggings (Leaf _)       = [[]]
      taggings (LOnly t)      = map (L:) (taggings t)
      taggings (ROnly t)      = map (R:) (taggings t)
      taggings (Branch lt rt) = map (L:) (taggings lt) ++ map (R:) (taggings rt)

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

  unlabelled Leaf{} = True
  unlabelled _ = False

instance Pretty (LTree Form) where
  pretty (Leaf e) = pretty e
  pretty (LOnly t) = pretty "L:" <> pretty t
  pretty (ROnly t) = pretty "R:" <> pretty t
  pretty (Branch t1 t2) = pretty "L:" <> pretty t1
                      <+> pretty "R:" <> pretty t2

