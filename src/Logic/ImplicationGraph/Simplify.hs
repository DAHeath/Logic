module Logic.ImplicationGraph.Simplify where

import           Control.Lens

import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G
import qualified Data.Set as S
import           Data.Foldable (toList)

import           Logic.Name
import           Logic.Formula
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.LTree as L

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
conj :: Name n => Form (Aliasable n) -> Form (Aliasable n) -> Form (Aliasable n)
conj e1 e2 =
  fmap unalias e1 `mkAnd` e2
    where
      unalias = \case
        Aliased n -> NoAlias n
        NoAlias n -> NoAlias n

disj :: Name n => Form n -> Form n -> Form n
disj = mkOr

conjunction :: Name n => Edge (Aliasable n) -> Edge (Aliasable n) -> Edge (Aliasable n)
conjunction e1 e2 =
  let inc = foldl1 disj (toList e1)
  in fmap (conj inc) e2

disjunction :: Name n => Edge n -> Edge n -> Edge n
disjunction = L.unionWith disj

-- | Remove all reducible vertices and combine edges through {dis/con}junction.
prune :: (Ord i) => Graph i (Edge BasicName) (Inst BasicName)
      -> Graph i (Edge BasicName) (Inst BasicName)
prune graph = foldr removeVertex graph reducible where
  andEdge (G.HEdge s1 e1, f1) (G.HEdge s2 e2, f2) =
    G.addEdgeWith disjunction
      (G.HEdge ((s2 S.\\ S.singleton e1) `S.union` s1) e2) $ conjunction f1 f2

  newEdges i g = cartesianProduct andEdge
                 ((toListOf $ G.iedgesTo   i . withIndex) g)
                 ((toListOf $ G.iedgesFrom i . withIndex) g)

  removeVertex i g = foldr ($) (G.delIdx i g) $ newEdges i g

  reducible = filter (not . flip elem (irreducible graph)) $ G.idxs graph
