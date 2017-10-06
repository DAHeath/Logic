{-# LANGUAGE LambdaCase #-}
module Data.Graph.Inductive.Extras where

import           Control.Monad.State

import           Data.Bifunctor (second)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Graph.Inductive.PatriciaTree
import           Data.Graph.Inductive.Graph
import           Data.Graph.Inductive.Basic
import           Data.Graph.Inductive.Query.DFS
import           Data.Graph.Inductive.Query.BFS

-- | A node is a duplicate of another if it is created by an unfolding. The
-- duplication map indicates what node the current node is a duplicate of.
type DuplicationMap = Map Node Node

dupLookup :: DuplicationMap -> Node -> Node
dupLookup m n =
  case M.lookup n m of
    Nothing -> n
    Just n' -> dupLookup m n'

-- | Unfold the graph with respect to a given backedge.
unfold :: Eq e => LEdge e -> Gr n e -> State DuplicationMap (Gr n e)
unfold (l1, l2, b) g =
  let g' = subgraphBetween l1 l2 g
      ns = nodes g'
      -- remove the edges which enter the expanded subgraph
      incoming = filter (\(l1', l2', _) -> l1' `notElem` ns && l2' `elem` ns) (labEdges g)
      outgoing = filter (\(l1', l2', _) -> l1' `elem` ns && l2' `notElem` ns) (labEdges g)
      incomingRemoved = efilter (`notElem` incoming) g
      -- relabel the subgraph
      (rel, dup) = relabelWithRespectTo g' g
      relabelled = relabel rel g'
      merged = overlay incomingRemoved relabelled
      connected = insEdge (rel l1, l2, b) merged
      incRerouted = foldr (\(l1', l2', b') gr -> insEdge (l1', rel l2', b') gr)
                          connected incoming
      outDuplicated = foldr (\(l1', l2', b') gr -> insEdge (rel l1', l2', b') gr)
                            incRerouted outgoing

  in do
    modify (M.union dup)
    return outDuplicated

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

relabelWithRespectTo :: DynGraph gr => gr n e -> gr n e -> (Node -> Node, DuplicationMap)
relabelWithRespectTo toRelabel toRespect =
  let ns = nodes toRelabel
      m = M.fromList (zip ns (newNodes (order toRelabel) toRespect))
      dup = M.fromList (zip (newNodes (order toRelabel) toRespect) ns)
  in (\n -> M.findWithDefault n n m, dup)

relabel :: DynGraph gr => (Node -> Node) -> gr n e -> gr n e
relabel rel g =
  gmap (\(adjl, l, n, adjr) -> ( map (second rel) adjl
                               , rel l
                               , n
                               , map (second rel) adjr)) g

removeBackedges :: Gr n e -> Gr n e
removeBackedges = efilter (\(l1, l2, _) -> l1 < l2)

backEdges :: Gr n e -> [LEdge e]
backEdges = filter (\(l1, l2, _) -> l2 <= l1) . labEdges

removeReaching :: DynGraph gr => Node -> gr n e -> gr n e
removeReaching l = efilter (\(_, l2, _) -> l2 /= l)

reverseReached :: DynGraph gr => Node -> gr n e -> gr n e
reverseReached n g = nfilter (`elem` (reachable n (grev g))) g
