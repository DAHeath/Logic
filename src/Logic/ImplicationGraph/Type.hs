{-# LANGUAGE TemplateHaskell #-}
module Logic.ImplicationGraph.Type where

import           Control.Lens hiding (Context)

import           Data.Data (Data)
import           Data.Ord.Graph
import           Data.Map (Map)
import qualified Data.Map as M

import           Logic.Formula
import           Logic.Var

import           Text.PrettyPrint.HughesPJClass as PP

type InstanceId = Int
type Lbl = Int

type Node = ([Lbl], InstanceId)

type Instance = ([[Var]], Form)

emptyInstance :: [Var] -> Instance
emptyInstance vs = ([vs], LBool True)

data ImplGrNode
  = AndNode
  | OrInputNode
  | OrOutputNode
  | InstanceNode Instance
  | QueryNode Form
  | FoldedNode Node
  deriving (Show, Read, Eq, Ord, Data)

makePrisms ''ImplGrNode

instance Pretty ImplGrNode where
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

type ImplGr = Graph Node ImplGrEdge ImplGrNode
