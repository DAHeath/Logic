module Logic.ImplicationGraph.Equivalence where

import           Control.Lens
import           Control.Monad.State

import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G
import qualified Data.Optic.Graph.Extras as G
import           Data.Text.Prettyprint.Doc
import           Data.These

import           Logic.Formula
import           Logic.Model
import           Logic.Var
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Induction
import           Logic.ImplicationGraph.Chc
import           Logic.ImplicationGraph.LTree
import           Logic.ImplicationGraph.Simplify

-- | Repeatedly unwind the program until a counterexample is found or inductive
-- invariants are found.
solve :: MonadIO m
      => Form
      -> Graph Loc Edge Inst
      -> Graph Loc Edge Inst
      -> m (Either Model ImplGr)
solve quer g1 g2 = loop $ fromGraph wQuery
  where
    e1 = end g1
    e2 = end g2
    wQuery =
      let g = equivProduct (prepare g1) (prepare g2)
          vs' = g ^?! ix (LocPair e1 e2) . instVars
      in
      g & G.addVert Terminal (Inst Terminal vs' quer)
        & G.addEdge (G.HEdge (S.singleton (LocPair e1 e2)) Terminal) (Leaf $ LBool True)
        & prune

    prepare g =
      let new = execState (G.idfsEdge_ (\(G.HEdge st end) e ->
            when (null st) $ modify ((G.HEdge (S.singleton Initial) end, e):)) g) []
      in
      g & G.ifilterEdges (\(G.HEdge st _) _ -> not $ null st)
        & G.addVert Initial (emptyInst Initial [])
        & flip (foldr (uncurry G.addEdge)) new

    equivProduct g1 g2 =
      cleanIntros (G.cartesianProductWith edgeMerge const LocPair vertMerge
                     (G.mapEdge LOnly g1)
                     (G.mapEdge ROnly g2))

    cleanIntros g =
      let es = g ^@.. G.iallEdges
      in G.delIdx start $ foldr (\(G.HEdge i1 i2, e) g ->
        G.addEdge (G.HEdge (S.filter (/= start) i1) i2) e (G.delEdge (G.HEdge i1 i2) g)) g es

    start = LocPair Initial Initial
    isStart = \case
      LocPair Initial _ -> True
      LocPair _ Initial -> True
      _ -> False

    edgeMerge (LOnly e1) (ROnly e2) = Br e1 e2
    edgeMerge e1 _ = e1

    vertMerge v1 v2 = case (v1, v2) of
      (Inst i vs1 _, Inst j vs2 _) ->
        emptyInst (LocPair i j) (vs1 ++ vs2)
