module Logic.Solver.Equivalence where

import           Control.Lens
import           Control.Monad.State

import           Data.Data (Data)
import           Data.Copointed
import qualified Data.Set as S
import           Data.Loc
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G

import           Logic.Formula
import           Logic.ImplicationGraph

-- | Repeatedly unwind the program until a counterexample is found or inductive
-- invariants are found.
solve :: (MonadIO m, Copointed e1, Data (e1 Form))
      => Form
      -> Graph Loc (e1 Form) Inst
      -> Graph Loc (e1 Form) Inst
      -> m (Either Model (ImplGr LTree))
solve quer g1 g2 =

  loop $ fromGraph wQuery
  where
    g1' = g1 & vars . varId %~ ("l":)
    g2' = g2 & vars . varId %~ ("r":)
    wQuery = query quer $ equivProduct (prepare g1') (prepare g2')

    prepare g =
      let new = execState (G.idfsEdges_ (\(G.HEdge st edgeEnd) e ->
            when (null st) $ modify ((G.HEdge (S.singleton Initial) edgeEnd, e):)) g) []
      in
      g & G.ifilterEdges (\(G.HEdge st _) _ -> not $ null st)
        & G.addVert Initial (emptyInst Initial [])
        & flip (foldr (uncurry G.addEdge)) new

    equivProduct g1'' g2'' =
      cleanIntros (G.cartesianProductWith edgeMerge const LocPair vertMerge
                     (G.mapEdges (LOnly . Leaf . copoint) g1'')
                     (G.mapEdges (ROnly . Leaf . copoint) g2''))

    cleanIntros = G.delIdxSaveEdges (\_ _ -> True) start
    start = LocPair Initial Initial

    edgeMerge (LOnly e1') (ROnly e2') = Branch e1' e2'
    edgeMerge e1' _ = e1'

    vertMerge v1 v2 = case (v1, v2) of
      (Inst i vs1 _, Inst j vs2 _) ->
        emptyInst (LocPair i j) (vs1 ++ vs2)
