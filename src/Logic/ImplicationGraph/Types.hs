{-# LANGUAGE DeriveDataTypeable
           , TypeFamilies
           , TemplateHaskell
           , ConstraintKinds
           , FlexibleInstances #-}
module Logic.ImplicationGraph.Types where

import           Control.Lens
import           Control.Arrow (first)

import           Data.Data
import           Data.Text.Prettyprint.Doc
import           Data.Optic.Directed.HyperGraph (Graph)

import           Logic.Var
import           Logic.Formula
import           Logic.ImplicationGraph.LTree

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

type Edge = LTree Form

instance Pretty (LTree Form) where
  pretty (Leaf e) = pretty e
  pretty (LOnly t) = pretty "L:" <> pretty t
  pretty (ROnly t) = pretty "R:" <> pretty t
  pretty (Branch t1 t2) = pretty "L:" <> pretty t1
                      <+> pretty "R:" <> pretty t2

instance Pretty Inst where
  pretty (Inst l vs f) = pretty l <+> pretty vs <+> pretty f

type ImplGr = Graph Idx Edge Inst

