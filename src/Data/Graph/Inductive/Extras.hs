{-# LANGUAGE LambdaCase #-}
module Data.Graph.Inductive.Extras where

import           Data.Bifunctor (second)
import qualified Data.Map as M
import           Data.Graph.Inductive.PatriciaTree
import           Data.Graph.Inductive.Graph
import           Data.Graph.Inductive.Basic
import           Data.Graph.Inductive.Query.BFS

-- | Unfold the graph with respect to a given backedge.
unfold :: Eq e => LEdge e -> Gr n e -> Gr n e
unfold (l1, l2, b) g =
  let g' = subgraphBetween l1 l2 g
      ns = nodes g'
      -- remove the edges which enter the expanded subgraph
      toReroute = filter (\(l1', l2', _) -> l1' `notElem` ns && l2' `elem` ns) (labEdges g)
      reroutesRemoved = efilter (`notElem` toReroute) g
      -- relabel the subgraph
      rel = relabelWithRespectTo g' g
      relabelled = relabel rel g'
      merged = overlay reroutesRemoved relabelled
      connected = insEdge (rel l1, l2, b) merged
      rerouted = foldr (\(l1', l2', b') gr -> insEdge (l1', rel l2', b') gr)
                       connected toReroute
  in rerouted

-- | Combine two graphs
overlay :: DynGraph gr => gr n e -> gr n e -> gr n e
overlay g g' = foldr insEdge (foldr insNode g (labNodes g')) (labEdges g')

subgraphBetween :: Node -> Node -> Gr n e -> Gr n e
subgraphBetween l1 l2 g =
  let simpl = removeBackedges $ removeReaching l2 g
      rev = grev simpl
      allPs = bft l1 rev
      ps = concat $ filter (\case
                             [] -> False
                             ls -> head ls == l2 && last ls == l1) allPs
  in subgraph ps simpl

relabelWithRespectTo :: DynGraph gr => gr n e -> gr n e -> Node -> Node
relabelWithRespectTo toRelabel toRespect =
  let ns = nodes toRelabel
      m = M.fromList (zip ns (newNodes (order toRelabel) toRespect))
  in \n -> M.findWithDefault undefined n m

relabel :: DynGraph gr => (Node -> Node) -> gr n e -> gr n e
relabel rel g =
  gmap (\(adjl, l, n, adjr) -> ( map (second rel) adjl
                               , rel l
                               , n
                               , map (second rel) adjr)) g

removeBackedges :: Gr n e -> Gr n e
removeBackedges = efilter (\(l1, l2, _) -> l1 < l2)

backEdges :: Gr n e -> [LEdge e]
backEdges = filter (\(l1, l2, _) -> l2 < l1) . labEdges

removeReaching :: DynGraph gr => Node -> gr n e -> gr n e
removeReaching l = efilter (\(_, l2, _) -> l2 /= l)
