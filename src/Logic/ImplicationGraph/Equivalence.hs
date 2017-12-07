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
      => Loc
      -> Loc
      -> Form
      -> Graph Loc Form Inst
      -> Graph Loc Form Inst
      -> m (Either Model ImplGr)
solve e1 e2 quer g1 g2 = do
  G.display "before" wQuery
  let gr = fromGraph wQuery
  loop gr
  where
    wQuery = equivProduct g1 g2 & ix (LocPair e1 e2) . instForm .~ quer

    equivProduct g1 g2 =
      let g = cleanIntros (G.cartesianProductWith edgeMerge const LocPair vertMerge
                           (G.mapEdge (LOnly . Leaf) g1)
                           (G.mapEdge (ROnly . Leaf) g2))
      in G.imapEdge (edgeVarLocAugment g) g

    cleanIntros g =
      let es = g ^@.. G.iallEdges
      in G.delIdx start $ foldr (\(G.HEdge i1 i2, e) g ->
        G.addEdge (G.HEdge (S.filter (/= start) i1) i2) e (G.delEdge (G.HEdge i1 i2) g)) g es

    start = LocPair (Loc 0) (Loc 0)

    edgeMerge (LOnly e1) (ROnly e2) = Br e1 e2
    edgeMerge e1 _ = e1

    vertMerge v1 v2 = case (v1, v2) of
      (Inst i vs1 _, Inst j vs2 _) ->
        emptyInst (LocPair i j) (vs1 ++ vs2) & vars %~ setLoc (LocPair i j)

    setLoc l = mapLoc (const l)

    mapLoc f = \case
      Free (FreeV n l b) t -> Free (FreeV n (f l) b) t
      Bound n t -> Bound n t

    edgeVarLocAugment :: Graph Loc (LTree Form) Inst -> G.HEdge Loc -> LTree Form -> LTree Form
    edgeVarLocAugment g (G.HEdge is i) e =
      let e' = if null is
               then e & vars %~ setLoc (g ^?! ix i . instLoc)
               else case (S.findMin is, i) of
                 (LocPair i j, LocPair i' j') ->
                   if i == i'
                   then e & vars %~ mapLoc (LocPair i)
                   else e & vars %~ mapLoc (`LocPair` j)
          -- the variables which are not mentioned in the edge
          absentVars = S.fromList (g ^?! ix i . instVars) `S.difference` varSet e'
          inInc = S.fromList $ concatMap (\i -> g ^?! ix i . instVars) (S.toList is)
          toReassign = absentVars `S.intersection` inInc
      in
      e'
