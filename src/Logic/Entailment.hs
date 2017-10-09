{-# LANGUAGE TemplateHaskell #-}
module Logic.Entailment where

import           Control.Lens hiding (Context)
import           Control.Monad.State

import           Data.Data (Data)
import           Data.Graph.Inductive.Basic
import           Data.Graph.Inductive.Graph
import           Data.Graph.Inductive.PatriciaTree
import           Data.Graph.Inductive.Extras
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Tree (Tree)
import qualified Data.Tree as T
import           Data.Maybe (mapMaybe)
import           Data.Foldable (foldrM)

import           Logic.Var
import           Logic.Formula

import           Text.PrettyPrint.HughesPJClass as PP

type InstanceId = Int
type Lbl = Int

data Inductive
  = NotInductive
  | UnknownIfInductive
  | InductiveSucc
  | InductiveFalse
  | InductiveBy InstanceId
  deriving (Show, Eq, Ord, Data)

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
  , _variables :: Set Var
  , _formula :: Form
  , _inductive :: Inductive
  } deriving (Show, Eq, Ord, Data)

instance Pretty Instance where
  pPrint (Instance ids ins vs f ind) =
    hsep [pPrint ids, pPrint ins, pPrint (S.toList vs), pPrint f, pPrint ind]

mkInstance :: [Lbl] -> Set Var -> Instance
mkInstance ids vs = Instance ids 0 vs (LBool True) UnknownIfInductive

makeLenses ''Instance

data EntailmentNode
  = AndNode
  | OrNode
  | InstanceNode Instance
  | QueryNode Form
  deriving (Show, Eq, Ord, Data)

instance Pretty EntailmentNode where
  pPrint = \case
    AndNode -> text "AND"
    OrNode -> text "OR"
    InstanceNode i -> pPrint i
    QueryNode f -> pPrint f

data EntailmentEdge = EntailmentEdge Form (Map Var Var)
  deriving (Show, Eq, Ord, Data)

instance Pretty EntailmentEdge where
  pPrint (EntailmentEdge f m) = pPrint f <+> pPrint (M.toList m)

type Entailment = Gr EntailmentNode EntailmentEdge

backEdges :: [Int] -> Entailment -> [LEdge EntailmentEdge]
backEdges dims g = S.toList $ ufold (\c s -> s `S.union` ctxSet c) S.empty g
  where
    ctxSet :: Context EntailmentNode EntailmentEdge -> Set (LEdge EntailmentEdge)
    ctxSet (bef, n, here, aft) =
      let befSets = mapMaybe (\(e, n') -> do
                                l <- lab g n'
                                return (backEdgeSet e (n', l) (n, here))) bef
          aftSets = mapMaybe (\(e, n') -> do
                                l <- lab g n'
                                return (backEdgeSet e (n, here) (n', l))) aft
      in S.unions (befSets ++ aftSets)

    backEdgeSet :: EntailmentEdge
                -> LNode EntailmentNode
                -> LNode EntailmentNode
                -> Set (LEdge EntailmentEdge)
    backEdgeSet e (n1, l1) (n2, l2) = case (l1, l2) of
      (InstanceNode l1', InstanceNode l2') ->
        if (l2' ^. identity) `leq` (l1' ^. identity)
        then S.singleton (n1, n2, e)
        else S.empty
      _ -> S.empty

    leq :: [Lbl] -> [Lbl] -> Bool
    leq x y = loc dims x <= loc dims y

loc :: [Int] -> [Lbl] -> Int
loc dims = sum . zipWith dimension [0..]
  where
    dimension dim i = i * product (take dim dims)

factTree :: Entailment -> Tree (Node, Form)
factTree = undefined

unfolding allBes bes g =
  let g' = evalState (foldrM unfold g bes) M.empty
      g'' = efilter (`notElem` allBes) g'
  in treeFrom 0 g''
