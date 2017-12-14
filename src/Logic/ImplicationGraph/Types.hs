module Logic.ImplicationGraph.Types where

import           Control.Lens
import           Control.Arrow (first)

import           Data.Data
import           Data.Pointed
import           Data.Copointed
import           Data.Text.Prettyprint.Doc
import           Data.Loc
import           Data.Optic.Directed.HyperGraph (Graph)

import           Logic.Formula

-- | Inst indexes are arranged backwards -- newer instances which occur
-- closer to the beginning of the graph have higher value.
newtype Idx = Idx { getIdx :: Integer }
  deriving (Eq, Data, Num, Pretty, Integral, Real, Enum)
instance Ord Idx where Idx a <= Idx b = b <= a
instance Show Idx where show (Idx a) = show a
instance Read Idx where readsPrec i = map (first Idx) . readsPrec i

data Inst = Inst
  { _instLoc :: Loc
  , _instVars :: [Var]
  , _instForm :: Form
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Inst

instance Pretty Inst where
  pretty (Inst l vs f) = vsep [pretty l, pretty vs, pretty f]

type ImplGr f = Graph Idx (f Form) Inst

class (Copointed f, Pointed f, Traversable f) => Edge f where
  split :: f a -> [f a]
  collect :: [f a] -> [[a]]
  unlabelled :: f a -> Bool
  unionWith :: (a -> a -> a) -> f a -> f a -> f a

instance Edge Identity where
  split x = [x]
  collect = map (\(Identity x) -> [x])
  unlabelled = const True
  unionWith f (Identity x) (Identity y) = Identity (f x y)

instance Pretty x => Pretty (Identity x) where
  pretty (Identity x) = pretty x
