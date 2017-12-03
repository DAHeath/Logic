module Logic.ImplicationGraph.Simplify where

import           Control.Lens

import qualified Data.Map as Map
import           Data.Maybe
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G
import qualified Data.Set as S
import           Data.Foldable (toList)

import qualified Logic.Var as V
import           Logic.Var (Var, Name, Counted)
import qualified Logic.Type as T
import           Logic.Formula
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.LTree as L


type RenameMap n = Map.Map (Var n) (Var n)


-- | Finds irreducible vertices in a given `ImplGr`.
irreducible :: (Ord i) => Graph i e v -> [i]
irreducible graph = queryIndex : loopHeaders where
  idxs = G.idxs graph
  queryIndex = maximum idxs

  -- Find the loop headers, i.e. the destination vertices of back edges.
  loopHeaders = map (\(G.HEdge _ s, _) -> s) $ G.backEdges graph


-- | Takes the Cartesian product of two lists and with the product function.
cartesianProduct :: (a -> b -> c) -> [a] -> [b] -> [c]
cartesianProduct f as bs = [ f a b | a <- as, b <- bs ]


-- | Combine edges that 'execute' after one another, the first argument is
-- the edge that runs first.
conjunction :: Edge Counted -> Edge Counted -> Edge Counted
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


disjunction :: Name n => Edge n -> Edge n -> Edge n
disjunction e1 e2 =
  let
    combinedMap = combine (_edgeMap e1) (_edgeMap e2)
  in
    Edge {
      _edgeForm = mkOr (fitEdge e1 combinedMap) (fitEdge e2 combinedMap),
      _edgeMap = combinedMap
    }
  where
    combine :: Name n => RenameMap n -> RenameMap n -> RenameMap n
    combine = Map.unionWith max

    maxTemporality :: Name n => Var n -> RenameMap n -> Var n
    maxTemporality v rm = fromMaybe v $ max v <$> Map.lookup v rm

    fitEdge :: V.Name n => Edge n -> RenameMap n -> Form n
    fitEdge e rm = foldr folder (_edgeForm e) (Map.toList $ _edgeMap e)
      where
      eqlForm v' v = Eql (T.typeOf v) :@ V v' :@ V v

      folder (k, v) f = let v' = maxTemporality k rm in
        if v' > v then mkAnd (eqlForm v' v) f else f

lconjunction :: LEdge Counted -> LEdge Counted -> LEdge Counted
lconjunction e1 e2 =
  let inc = foldl1 disjunction (toList e1)
  in fmap (conjunction inc) e2

ldisjunction :: Name n => LEdge n -> LEdge n -> LEdge n
ldisjunction = L.unionWith disjunction

-- | Remove all reducible vertices and combine edges through {dis/con}junction.
prune :: (Ord i) => Graph i (LEdge Counted) (Inst Counted)
      -> Graph i (LEdge Counted) (Inst Counted)
prune graph = foldr removeVertex graph reducible where
  andEdge (G.HEdge start end', e) (G.HEdge s' end, e') =
    G.addEdgeWith ldisjunction
      (G.HEdge ((s' S.\\ S.singleton end') `S.union` start) end) $ lconjunction e e'

  newEdges i g = cartesianProduct andEdge
                 ((toListOf $ G.iedgesTo i . withIndex) g)
                 ((toListOf $ G.iedgesFrom i . withIndex) g)

  removeVertex i g = foldr ($) (G.delIdx i g) $ newEdges i g

  reducible = filter (not . flip elem (irreducible graph)) $ G.idxs graph
