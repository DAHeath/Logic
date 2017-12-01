module Logic.ImplicationGraph.StackFragments where

import           Control.Lens

import           Data.Maybe (fromJust)
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G
import qualified Data.Optic.Graph.Extras as G
import qualified Data.Set as S


import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.LTree
import           Logic.Formula as F

import qualified Data.Map as M

import Debug.Trace

-- | Calculate the implication graph that also has stack fragments.
--
-- For each hyperedge add a new non-hyperedge from the pair of locations
fragmented :: ImplGr -> ImplGr
fragmented = undefined

hyperEdge :: Loc -> Loc -> Loc -> Graph Loc LEdge Inst -> Graph Loc LEdge Inst
hyperEdge i1 i2 tar g =
  let o = G.order g
      g1 = G.reaches i1 (G.withoutBackEdges g)
      g2 = G.reaches i2 (G.withoutBackEdges g)
      cp = G.cartesianProduct LocPair combineInst
                   (G.mapEdge LOnly g1)
                   (G.mapEdge ROnly g2)
      e = g ^?! G.edge (G.HEdge (S.fromList [i1, i2]) tar)
  in
  mappend cp g
  & G.addEdge (G.HEdge (S.singleton (LocPair i1 i2)) tar) (LOnly e)
  & flip (foldr cross) (G.idxs cp)
  where
    combineInst (Inst i vs1 _) (Inst j vs2 _) = emptyInst (LocPair i j) (vs1 ++ vs2)
    cross (LocPair i j) = G.addEdge (G.HEdge (S.fromList [i, j]) (LocPair i j)) (Leaf $ Edge (LBool True) M.empty)
    cross _ = id

g :: Graph Loc Edge Inst
g = G.fromLists
  [ (Loc 0, emptyInst (Loc 0) [])
  , (Loc 1, emptyInst (Loc 1) [])
  , (Loc 2, emptyInst (Loc 2) [])
  , (Loc 3, emptyInst (Loc 3) [])
  ]
  [ (G.HEdge S.empty (Loc 0), Edge (LBool True) M.empty)
  , (G.HEdge (S.singleton (Loc 0)) (Loc 0), Edge (LBool True) M.empty)
  , (G.HEdge (S.singleton (Loc 0)) (Loc 1), Edge (LBool True) M.empty)
  , (G.HEdge S.empty (Loc 2), Edge (LBool True) M.empty)
  , (G.HEdge (S.fromList [Loc 1, Loc 2]) (Loc 3), Edge (LBool True) M.empty)
  ]

test :: IO ()
test = do
  G.display "before" g
  G.display "after" (hyperEdge (Loc 1) (Loc 2) (Loc 3) (G.mapEdge Leaf g))
