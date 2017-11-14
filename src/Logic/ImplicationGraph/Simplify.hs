module Logic.ImplicationGraph.Simplify where

import           Control.Lens

import qualified Data.Map as Map
import           Data.Maybe
import           Data.Optic.Graph (Graph)
import qualified Data.Optic.Graph as G

import qualified Logic.Var as V
import qualified Logic.Type as T
import           Logic.Formula
import           Logic.ImplicationGraph


type RenameMap = Map.Map V.Var V.Var


-- | Finds irreducible vertices in a given `ImplGr`.
irreducible :: (Ord i) => Graph i Edge Vert -> [i]
irreducible graph = [startIndex, queryIndex] ++ loopHeaders where
  idxs = G.idxs graph
  startIndex = minimum idxs
  queryIndex = maximum idxs

  -- Find the loop headers, i.e. the destination vertices of back edges.
  loopHeaders = map (\((_, s), _) -> s) $ G.backEdges graph


-- | Takes the Cartesian product of two lists and with the product function.
cartesianProduct :: (a -> b -> c) -> [a] -> [b] -> [c]
cartesianProduct f as bs = [ f a b | a <- as, b <- bs ]


-- | Combine edges that 'execute' after one another, the first argument is
-- the edge that runs first.
conjunction :: Edge -> Edge -> Edge
conjunction edge edge' =
  let
    bumpVarBy bumper var =
      V.bumpVar ((+) $ fromMaybe 0 $ Map.lookup (V.varPath var) bumper) var

    conflicts = Map.mapKeys V.varPath $
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
disjunction e1 e2 =
  let
    combinedMap = combine (_edgeMap e1) (_edgeMap e2)
  in
    Edge {
      _edgeForm = mkOr (fitEdge e1 combinedMap) (fitEdge e2 combinedMap),
      _edgeMap = combinedMap
    }
  where
    combine :: RenameMap -> RenameMap -> RenameMap
    combine = Map.unionWith max

    maxTemporality :: V.Var -> RenameMap -> V.Var
    maxTemporality v rm = fromMaybe v $ max v <$> Map.lookup v rm

    fitEdge :: Edge -> RenameMap -> Form
    fitEdge e rm = foldr folder (_edgeForm e) (Map.toList $ _edgeMap e)
      where
      eqlForm v' v = Eql (T.typeOf v) :@ V v' :@ V v

      folder (k, v) f = let v' = maxTemporality k rm in
        if v' > v then mkAnd (eqlForm v' v) f else f


-- | Remove all reducible vertices and combine edges through {dis/con}junction.
prune :: (Ord i) => Graph i Edge Vert -> Graph i Edge Vert
prune graph = foldr removeVertex graph reducible where
  andEdge (start, e) (end, e') =
    G.addEdgeWith disjunction start end $ conjunction e e'

  newEdges i g = cartesianProduct andEdge
                 ((toListOf $ G.iedgesTo i . withIndex) g)
                 ((toListOf $ G.iedgesFrom i . withIndex) g)

  removeVertex i g = foldr ($) (G.delIdx i g) $ newEdges i g

  reducible = filter (not . flip elem (irreducible graph)) $ G.idxs graph
