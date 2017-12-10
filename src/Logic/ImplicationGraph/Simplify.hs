module Logic.ImplicationGraph.Simplify where

import           Control.Lens

import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G
import qualified Data.Set as S
import           Data.Foldable (toList)
import           Data.Text.Prettyprint.Doc

import           Logic.Formula
import           Logic.Var
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.LTree as L

import Debug.Trace

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
conj :: Form -> Form -> Form
conj e1 e2 =
  mapVars unalias e1 `mkAnd` e2
    where
      unalias = \case
        Bound b t -> Bound b t
        Free (FreeV n l _) t -> Free (FreeV n l False) t

disj :: Form -> Form -> Form
disj = mkOr

conjunction :: Edge -> Edge -> Edge
conjunction e1 e2 =
  let inc = foldl1 disj (toList e1)
  in fmap (conj inc) e2

disjunction :: Edge -> Edge -> Edge
disjunction = L.unionWith disj

-- | Remove all reducible vertices and combine edges through {dis/con}junction.
prune :: (Show i, Ord i) => Graph i Edge Inst
      -> Graph i Edge Inst
prune graph =
  let g = foldl (flip removeVertex) graph reducible
  in G.imapEdge (cleanEdgeVars g) g
  where
  andEdge (G.HEdge s1 e1, f1) (G.HEdge s2 e2, f2) =
    G.addEdgeWith disjunction
      (G.HEdge ((s2 S.\\ S.singleton e1) `S.union` s1) e2) $ conjunction f1 f2

  newEdges i g =
    trace (show i ++ concatMap (show . pretty) (g ^.. G.iedgesTo i)) $
    cartesianProduct andEdge
      ((toListOf $ G.iedgesTo   i . withIndex) g)
      ((toListOf $ G.iedgesFrom i . withIndex) g)

  removeVertex i g = trace ("removing " ++ show i) $
    foldr ($) (G.delIdx i g) $ newEdges i g

  reducible = filter (not . flip elem (irreducible graph)) $ G.idxs graph

  cleanEdgeVars :: Ord i => Graph i Edge Inst -> G.HEdge i -> Edge -> Edge
  cleanEdgeVars g (G.HEdge is i) e =
    let vsBef = concatMap (\i' -> g ^?! ix i' . instVars) is
        vsAft = ((g ^?! ix i . instVars) & map setNew)
                ++ (g ^?! ix i . instVars)
        conserve = S.fromList (vsBef ++ vsAft)
    in fmap (varElim conserve) e

  setNew v = v & _Free . _1 . freeVNew .~ True
