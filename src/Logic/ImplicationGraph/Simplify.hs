module Logic.ImplicationGraph.Simplify where

import           Control.Lens

import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G
import qualified Data.Set as S
import           Data.Copointed

import           Logic.Formula
import           Logic.ImplicationGraph.Types as T

-- | Finds irreducible vertices in a given `ImplGr`.
irreducible :: (Ord i) => Graph i e v -> [i]
irreducible graph = queryIndex : loopHeaders where
  idxs = G.idxs graph
  queryIndex = maximum idxs

  -- Find the loop headers, i.e. the destination vertices of back edges.
  loopHeaders = map (\(G.HEdge is s, _) ->
    if length is > 1 then maximum is
    else s) $ G.backEdges graph


-- | Takes the Cartesian product of two lists and with the product function.
cartesianProduct :: (a -> b -> c) -> [a] -> [b] -> [c]
cartesianProduct f as bs = [ f a b | a <- as, b <- bs ]

-- | Combine edges that 'execute' after one another, the first argument is
-- the edge that runs first.
conjunction :: Edge f => f Form -> f Form -> f Form
conjunction e1 e2 =
  if unlabelled e2
  -- preserve the structure of the incoming edge if
  -- the outgoing edge has no structure
  then fmap (mkAnd (copoint e2)) (e1 & traverse . vars %~ unalias)
  else fmap (conj (manyOr e1)) e2

  where
    conj a b = mapVars unalias a `mkAnd` b
    unalias v = v & varNew .~ False

disjunction :: Edge f => f Form -> f Form -> f Form
disjunction = T.unionWith mkOr

-- | Remove all reducible vertices and combine edges through {dis/con}junction.
prune :: (Show i, Ord i, Edge f) => Graph i (f Form) Inst
      -> Graph i (f Form) Inst
prune graph =
  let g = foldl (flip removeVertex) graph reducible
  in G.imapEdges (cleanEdgeVars g) g
  where
    andEdge (G.HEdge s1 e1, f1) (G.HEdge s2 e2, f2) =
      (G.HEdge ((s2 S.\\ S.singleton e1) `S.union` s1) e2, conjunction f1 f2)

    newEdges i g =
      cartesianProduct andEdge
        ((toListOf $ G.iedgesTo   i . withIndex) g)
        ((toListOf $ G.iedgesFrom i . withIndex) g)

    removeVertex i g =
      -- There is a special case for removing vertices caused by hyperedges.
      -- Specifically, if there is a hyperedge to a target that includes
      -- some vertex `v` and another predecessor and that predecessor also
      -- has `v` as a child, then the target is irreducible.
      if any (isSpecialCase g . fst) (g ^@.. G.iedgesFrom i)
      then g
      else
        foldr (uncurry (G.addEdgeWith disjunction)) (G.delIdx i g) (newEdges i g)

    isSpecialCase g (G.HEdge is i) = any (isSpecialPred g is i) is

    isSpecialPred g is i j =
      let inter = G.predecessors g j `S.intersection` is in
      not (null inter || inter == S.singleton j)

    reducible = filter (not . flip elem (irreducible graph)) $ G.idxs graph

    cleanEdgeVars :: (Edge f, Ord i)
                  => Graph i (f Form) Inst -> G.HEdge i -> f Form -> f Form
    cleanEdgeVars g (G.HEdge is i) e =
      let vsBef = concatMap (\i' -> g ^?! ix i' . instVars) is
          vsAft = ((g ^?! ix i . instVars) & map setNew) ++ (g ^?! ix i . instVars)
          conserve = S.fromList (vsBef ++ vsAft)
      in fmap (varElim conserve) e

    setNew v = v & varNew .~ True
