module Logic.ImplicationGraph.Simplify where

import           Control.Lens

import qualified Data.Map as Map
import           Data.Maybe
import qualified Data.Optic.Graph as G

import qualified Logic.Var as V
import           Logic.Formula
import           Logic.ImplicationGraph


-- | Finds irreducible vertices in a given `ImplGr`.
irreducible :: (Ord i) => ImplGr i -> [i]
irreducible graph = [startIndex, queryIndex] ++ loopHeaders where
  idxs = G.idxs graph
  startIndex = minimum idxs
  queryIndex = maximum idxs

  -- Find the loop headers, i.e. the destination vertices of back edges.
  loopHeaders = map (\((_, s), _) -> s) $ G.backEdges graph


cartesianProduct :: (a -> b -> c) -> [a] -> [b] -> [c]
cartesianProduct f as bs = [ f a b | a <- as, b <- bs ]


conjunction :: Edge -> Edge -> Edge
conjunction edge edge' =
  let
    bumpVarBy bumper var =
      V.bumpVar ((+) $ fromMaybe 0 $ Map.lookup (V.path var) bumper) var

    conflicts = Map.mapKeys V.path $
                Map.mapMaybe V.aliasCount $ _edgeMap edge
  in Edge {
    _edgeForm = mkAnd
                (_edgeForm edge)
                (mapVar (bumpVarBy conflicts) $ _edgeForm edge'),
    _edgeMap = Map.union
               (Map.map (bumpVarBy conflicts) $ _edgeMap edge')
               (_edgeMap edge)
    }


disjunction :: Edge -> Edge -> Edge
disjunction = undefined


prune :: (Ord i) => ImplGr i -> ImplGr i
prune graph = foldr removeVertex graph reducible where
  andEdge (start, e) (end, e') =
    G.addEdgeWith disjunction start end $ conjunction e e'

  newEdges i g = cartesianProduct andEdge
                 ((toListOf $ G.iedgesTo i . withIndex) g)
                 ((toListOf $ G.iedgesFrom i . withIndex) g)

  removeVertex i g = foldr ($) (G.delIdx i g) $ newEdges i g

  reducible = filter (`elem` irreducible graph) $ G.idxs graph
