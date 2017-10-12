{-# LANGUAGE TemplateHaskell #-}
module Logic.ImplicationGraph.Type where

import           Control.Lens hiding (Context)

import           Data.Data (Data)
import           Data.Graph.Inductive.Graph
import           Data.Graph.Inductive.PatriciaTree (Gr)
import           Data.Map (Map)
import qualified Data.Map as M

import           Logic.Formula
import           Logic.Var

import           Text.PrettyPrint.HughesPJClass as PP

type InstanceId = Int
type Lbl = Int

data Instance = Instance
  { _identity :: [Lbl]
  , _instanceId :: InstanceId
  , _variables :: [Var]
  , _formula :: Form
  } deriving (Show, Read, Eq, Ord, Data)

instance Pretty Instance where
  pPrint (Instance ids ins vs f) =
    hsep [pPrint ids, pPrint ins, pPrint vs, pPrint f]

makeLenses ''Instance

mkInstance :: [Lbl] -> [Var] -> Instance
mkInstance ids vs = Instance ids 0 vs (LBool True)

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

type ImplGr = Gr ImplGrNode ImplGrEdge
