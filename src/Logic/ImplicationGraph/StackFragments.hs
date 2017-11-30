module Logic.ImplicationGraph.StackFragments where

import           Control.Lens

import           Data.Maybe (fromJust)
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G
import qualified Data.Optic.Graph.Extras as G
import qualified Data.Set as S


import           Logic.ImplicationGraph
import           Logic.Formula as F

import qualified Data.Map as M

import Debug.Trace

-- | Calculate the implication graph that also has stack fragments.
--
-- For each hyperedge add a new non-hyperedge from the pair of locations
fragmented :: ImplGr e -> ImplGr e
fragmented = undefined

hyperEdge :: Loc -> Loc -> Loc -> Graph Loc Edge Inst -> Graph Loc Edge Inst
hyperEdge i1 i2 tar g =
  let o = G.order g
      g1 = G.reaches i1 g
      g2 = G.reaches i2 g
      cp = G.cartesianProduct LocPair combineInst g1 g2
  in
  mappend cp g
  & G.addEdge (G.HEdge (S.singleton (LocPair i1 i2)) tar) (Edge (LBool True) M.empty)
  & flip (foldr cross) (G.idxs cp)
  where
    combineInst = const
    cross (LocPair i j) = G.addEdge (G.HEdge (S.fromList [i, j]) (LocPair i j)) (Edge (LBool True) M.empty)
    cross _ = id

g :: Graph Loc Edge Inst
g = G.fromLists
  [ (0, emptyInst 0 [])
  , (1, emptyInst 1 [])
  , (2, emptyInst 2 [])
  , (3, emptyInst 3 [])
  ]
  [ (G.HEdge S.empty 0, Edge (LBool True) M.empty)
  , (G.HEdge (S.singleton 0) 0, Edge (LBool True) M.empty)
  , (G.HEdge (S.singleton 0) 1, Edge (LBool True) M.empty)
  , (G.HEdge S.empty 2, Edge (LBool True) M.empty)
  , (G.HEdge (S.fromList [1, 2]) 3, Edge (LBool True) M.empty)
  ]

test :: IO ()
test = do
  G.display "before" g
  G.display "after" (hyperEdge 1 2 3 g)
