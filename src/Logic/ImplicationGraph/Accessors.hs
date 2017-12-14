{-# LANGUAGE NoMonomorphismRestriction #-}
module Logic.ImplicationGraph.Accessors where

import           Control.Lens
import           Control.Applicative.Backwards
import           Control.Monad.State

import           Data.Pointed
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Maybe (fromJust)
import           Data.Loc
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G

import           Logic.Formula
import qualified Logic.Solver.Z3 as Z3
import           Logic.ImplicationGraph.Types
import           Logic.ImplicationGraph.Simplify
import           Logic.ImplicationGraph.LTree

-- | Construct an implication graph by swapping the labels for proper instance labels.
fromGraph :: Ord i => Graph i e Inst -> Graph Idx e Inst
fromGraph g = snd $ relabel (Idx 0) g

-- | An instance which contains no formula.
emptyInst :: Loc -> [Var] -> Inst
emptyInst l vs = Inst l vs (LBool False)

-- | Gather all facts known about each instance of the same index together by disjunction.
collectAnswer :: MonadIO m => ImplGr f -> m (Map Loc Form)
collectAnswer g = traverse Z3.superSimplify $ execState (G.itravVert (\_ (Inst loc _ f) ->
  when (f /= LBool True) $ modify (M.insertWith mkOr loc f)) g) M.empty

-- | Unwind all backedges which do not reach an inductive vertex, then compress
-- the graph to only those vertices which reach the end.
unwindAll :: Edge f => Integral i => Set i -> Graph i (f a) v -> Graph Idx (f a) v
unwindAll ind g =
  let relevantBes = backs & filter (\be ->      -- a backedge is relevant if...
        be & fst & G.start                      -- we consider the start of the backedge and...
           & any (\i' -> g & G.withoutBackEdges -- when there are no backedges...
                           & G.reached i'       -- the subgraph reached by the start of the backedge...
                           & G.idxs             -- contains no inductive indices
                           & none (`elem` ind)))
  in g & flip (foldr unwind) relevantBes                          -- unwind all the relevant backedges
       & G.ifilterEdges (\i _ -> i `notElem` map fst relevantBes) -- filter out the old backedges
       & reachEndWithoutBackedge                                  -- select the portion which reaches the query
       & relabel (Idx 0) & snd                                    -- relabel to account for discarded indices
  where
    reachEndWithoutBackedge g' =
      let compressed = g'        -- find the subgraph which...
            & G.withoutBackEdges -- has no backedges...
            & G.reaches (end g)  -- and reaches the query
      in G.filterIdxs (`elem` G.idxs compressed) g'
    backs = concatMap (\(i, e) -> map ((,) i) (split e)) $ G.backEdges g

-- | Unwind the graph on the given backedge and update all instances in the unwinding.
unwind :: Integral i => (G.HEdge i, e) -> Graph i e v -> Graph i e v
unwind (G.HEdge i1 i2, e) g =
  let (m, g') = g                                       -- in order to calculate the unwound subgraph:
        & G.reaches i2                                  -- find the subgraph which reaches the end of backedge
        & G.union (foldMap (\i -> G.between i2 i g) i1) -- attach the subgraph between the ends of the backedge
        & relabel (G.order g)                           -- relabel all the instances
  in
  g & G.union g'                                  -- attach the unwound subgraph
    & G.delEdge (G.HEdge i1 i2)                   -- delete the old backedge
    & G.addEdge (G.HEdge (S.map (m M.!) i1) i2) e -- re-add the backedge as a forward edge from the unwound subgraph

-- | Relabel the vertices in the graph in reverse topological order. The new index
-- values are obtained from the state. The map used to relabel is also returned.
relabel :: (Num i, Ord i, Ord k) => i -> Graph k e v -> (Map k i, Graph i e v)
relabel idx g = evalState (do
  m <- execStateT (buildMapping g) M.empty
  return (m, G.mapIdx (m M.!) g)) idx
  where
    buildMapping g' =         -- To construct the relabelling map
      g' & G.withoutBackEdges -- consider the graph without backedges
         & G.itopVert_ update -- update the map in topological order
         & fromJust           -- we know there are no backedges since we removed them
         & forwards           -- run the updates forwards

    -- add an entry to the relabelling map (in backwards order)
    update i _ = Backwards (modify . M.insert i =<< lift freshIdx)

    -- use the state to create a fresh index
    freshIdx = state (\ins -> (ins, ins+1))

-- | Find the end (query) of the graph
end :: Ord i => Graph i e v -> i
end g =
  -- the query has no outgoing edges
  maximum $ filter
  (\i -> lengthOf (G.edgesFrom i) (G.withoutBackEdges g) == 0) (G.idxs g)

query :: Edge f => Form -> Graph Loc (f Form) Inst -> Graph Loc (f Form) Inst
query q g =
  let e = end g
      vs' = g ^?! ix e . instVars
      m = M.fromList $ map (\v -> (v & varLoc .~ 0, v)) vs'
      q' = subst m q
  in
  g & G.addVert Terminal (Inst Terminal vs' q')
    & G.addEdge (G.HEdge (S.singleton e) Terminal) (point $ LBool True)
    & prune
