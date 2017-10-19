{-# LANGUAGE DeriveDataTypeable, TypeFamilies, TemplateHaskell #-}
module Logic.ImplicationGraph.Type2 where

import           Control.Lens

import           Data.Data
import           Data.Ord.Graph (Graph)
import qualified Data.Ord.Graph as G
import qualified Data.Ord.Graph.Extras as G
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.List.Split (splitOn)

import           Logic.Formula
import           Logic.Var

import           Text.PrettyPrint.HughesPJClass
import           Text.Read (readMaybe)

data Inst idx
  = BaseInst [Var] Form
  | AndInst [idx] (Inst idx)
  | OrInst [[idx]] (Inst idx)
  deriving (Show, Read, Eq, Ord, Data)

data Vert idx
  = Instance (Inst idx)
  | Query Form
  | Folded idx
  deriving (Show, Read, Eq, Ord, Data)
makePrisms ''Vert

data Edge = Edge Form (Map Var Var)
  deriving (Show, Read, Eq, Ord, Data)

instance Pretty idx => Pretty (Vert idx) where
  pPrint = \case
    Instance i -> pPrint i
    Query f -> pPrint f
    Folded idx -> text "FOLD" <+> pPrint idx

instance Pretty idx => Pretty (Inst idx) where
  pPrint = \case
    BaseInst vs f -> pPrint vs <+> pPrint f
    AndInst idxs inner -> text "and" <+> pPrint idxs <+> pPrint inner
    OrInst idxs inner -> text "or" <+> pPrint idxs <+> pPrint inner

class (Show a, Ord a, Data a) => Idx a where
  type BaseIdx a
  baseIdx :: Lens' a (BaseIdx a)
  toPrefix :: a -> String
  fromPrefix :: String -> Maybe a
  inst :: Lens' a Integer

match :: (Idx a, Eq (BaseIdx a)) => a -> a -> Bool
match x y = x ^. baseIdx == y ^. baseIdx

data LinIdx = LinIdx { _linIden :: Integer, _linInst :: Integer }
  deriving (Show, Read, Eq, Ord, Data)
makeLenses ''LinIdx

instance Idx LinIdx where
  type BaseIdx LinIdx = Integer
  baseIdx = linIden
  toPrefix (LinIdx iden i) = show iden ++ "_" ++ show i
  fromPrefix s = case splitOn "_" s of
      [iden, i] -> LinIdx <$> readMaybe iden <*> readMaybe i
      _ -> Nothing
  inst = linInst

type ImplGr idx = Graph idx Edge (Vert idx)

test = G.fromLists
  [ (0, 'a')
  , (1, 'b')
  , (2, 'c')
  , (3, 'd')
  ]
  [ (0, 1, 'w')
  , (1, 2, 'x')
  , (2, 3, 'y')
  , (2, 4, 'z')
  ]
