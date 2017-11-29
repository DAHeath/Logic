module Logic.ImplicationGraph.Chc where

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Except

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Optic.Directed.HyperGraph as G
import           Data.Maybe (fromJust)

import           Logic.Model
import           Logic.Var
import           Logic.Chc
import           Logic.ImplicationGraph
import qualified Logic.Solver.Z3 as Z3

-- | Interpolate the facts in the graph using CHC solving to label the vertices
-- with fresh definitions.
interpolate :: (MonadError Model m, MonadIO m)
            => ImplGr Edge -> m (ImplGr Edge)
interpolate g = (`applyModel` g) <$> Z3.solveChc (implGrChc g)

-- | Convert the forward edges of the graph into a system of Constrained Horn Clauses.
implGrChc :: ImplGr Edge -> [Chc]
implGrChc g = map rule topConns
  where
    topConns = -- to find the graph connections in topological order...
      (g & G.withoutBackEdges                          -- remove backedges
         & G.itopEdge                                  -- for each edge...
            (\is e -> Identity (G.omap inspect is, e)) -- lookup the edge indexes
         & fromJust                                    -- we know the graph has no backedges
         & runIdentity) ^.. G.iallEdges                -- collect all the connections
      where
        inspect i = (i, g ^?! ix i)

    -- each hypergraph connection converts to a Horn Clause.
    rule (G.HEdge lhs (i, v), Edge f mvs) =
      let lhs' = map buildRel (S.toList lhs)
      in case lengthOf (G.iedgesFrom i) g of
        0 -> Query lhs' f (subst mvs (v ^. instForm))   -- If the target vertex has no successors, then it's a query
        _ -> Rule  lhs' f (subst mvs (buildRel (i, v))) -- Otherwise, the vertex is part of a rule.

    -- construct an applied predicate from the instance
    buildRel (i, v) = mkApp ('r' : _Show #i) (v ^. instVars)

-- | Augment the fact at each vertex in the graph by the fact in the model.
applyModel :: Model -> ImplGr Edge -> ImplGr Edge
applyModel model = G.imapVert applyInst
  where
    applyInst i v =
      v & instForm %~ (\f ->
          M.findWithDefault f i instMap -- replace the formula by the value in the map
        & instantiate (v ^. instVars))  -- replace the bound variables by the instance variables

    instMap = getModel model
      & M.filterWithKey (\k _ -> head (varName k) == 'r') -- only consider the instance predicates
      & M.mapKeys (read . tail . varName)                 -- convert the keys of the map to indexes

