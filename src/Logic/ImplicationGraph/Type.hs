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

data Inductive
  = NotInductive
  | UnknownIfInductive
  | InductiveSucc
  | InductiveFalse
  | InductiveBy Node
  deriving (Show, Read, Eq, Ord, Data)

instance Pretty Inductive where
  pPrint = \case
    NotInductive -> text "NOT-IND"
    UnknownIfInductive -> text "UNK-IND"
    InductiveSucc -> text "IND-BY-SUCC"
    InductiveFalse -> text "IND-BY-FALSE"
    InductiveBy i -> text "IND-BY-ENT" <+> pPrint i

data Instance = Instance
  { _identity :: [Lbl]
  , _instanceId :: InstanceId
  , _variables :: [Var]
  , _formula :: Form
  , _inductive :: Inductive
  } deriving (Show, Read, Eq, Ord, Data)

instance Pretty Instance where
  pPrint (Instance ids ins vs f ind) =
    hsep [pPrint ids, pPrint ins, pPrint vs, pPrint f, pPrint ind]

makeLenses ''Instance

mkInstance :: [Lbl] -> [Var] -> Instance
mkInstance ids vs = Instance ids 0 vs (LBool True) UnknownIfInductive

data ImplGrNode
  = AndNode Inductive
  | OrNode Inductive
  | InstanceNode Instance
  | QueryNode Form
  | FoldedNode Node
  deriving (Show, Read, Eq, Ord, Data)

makePrisms ''ImplGrNode

instance Pretty ImplGrNode where
  pPrint = \case
    AndNode i -> text "AND" <+> pPrint i
    OrNode i -> text "OR" <+> pPrint i
    InstanceNode i -> pPrint i
    QueryNode f -> pPrint f
    FoldedNode n -> text "FOLDED" <+> pPrint n

data ImplGrEdge = ImplGrEdge Form (Map Var Var)
  deriving (Show, Read, Eq, Ord, Data)

instance Pretty ImplGrEdge where
  pPrint (ImplGrEdge f m) = pPrint f <+> pPrint (M.toList m)

type ImplGr = Gr ImplGrNode ImplGrEdge
