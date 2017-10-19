{-# LANGUAGE TemplateHaskell, TypeFamilies #-}
module Logic.ImplicationGraph.Type where

import           Control.Lens hiding (Context)

import           Data.Data (Data)
import           Data.Ord.Graph
import           Data.Map (Map)
import qualified Data.Map as M

import           Logic.Formula
import           Logic.Var

import           Text.PrettyPrint.HughesPJClass as PP
import           Text.Read (readMaybe)

type InstanceId = Int
type Lbl = Int

class (Show a, Ord a, Data a) => LblLike a where
  type Base a
  toBase :: a -> Base a
  match :: a -> a -> Bool
  toPrefix :: a -> String
  fromPrefix :: ReadS a

instance LblLike Int where
  type Base Int = Int
  toBase = id
  match x y = toBase x == toBase y
  toPrefix = show
  fromPrefix = reads

type Node' lbl = (lbl, InstanceId)
type Node = Node' Lbl

nodePrefix :: LblLike lbl => Node' lbl -> String
nodePrefix (l, i) = toPrefix l ++ "_" ++ show i

type Instance = ([[Var]], Form)

emptyInstance :: [Var] -> Instance
emptyInstance vs = ([vs], LBool True)

data ImplGrNode' lbl
  = AndNode
  | OrInputNode
  | OrOutputNode
  | InstanceNode Instance
  | QueryNode Form
  | FoldedNode (Node' lbl)
  deriving (Show, Read, Eq, Ord, Data)

makePrisms ''ImplGrNode'

type ImplGrNode = ImplGrNode' Lbl

instance Pretty lbl => Pretty (ImplGrNode' lbl) where
  pPrint = \case
    AndNode -> text "AND"
    OrInputNode -> text "OR-IN"
    OrOutputNode -> text "OR-OUT"
    InstanceNode i -> pPrint i
    QueryNode f -> pPrint f
    FoldedNode n -> text "FOLDED" <+> pPrint n

data ImplGrEdge = ImplGrEdge Form (Map Var Var)
  deriving (Show, Read, Eq, Ord, Data)

instance Pretty ImplGrEdge where
  pPrint (ImplGrEdge f m) = pPrint f <+> pPrint (M.toList m)

type ImplGr' lbl = Graph (Node' lbl) ImplGrEdge (ImplGrNode' lbl)
type ImplGr = ImplGr' Lbl
