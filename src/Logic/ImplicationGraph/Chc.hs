{-# LANGUAGE ScopedTypeVariables #-}
module Logic.ImplicationGraph.Chc where

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Except

import           Data.Data (Data)
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G
import           Data.Maybe (fromJust)
import           Data.Text.Prettyprint.Doc
import           Data.List.Split (splitOn)

import           Logic.Formula
import           Logic.Model
import           Logic.Var
import           Logic.Chc
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.LTree
import qualified Logic.Solver.Z3 as Z3

-- | Interpolate the facts in the graph using CHC solving to label the vertices
-- with fresh definitions.
interpolate :: (MonadError Model m, MonadIO m)
            => ImplGr -> m ImplGr
interpolate g = do
  let g' = G.withoutBackEdges (G.mapEdge point g)
  sol <- interp (G.reaches (end g') g')
  let vs = sol ^@.. G.iallVerts
  return $ foldr (\(i', v') g' -> G.addVert i' v' g') g vs
  where
    interp g' = do
      liftIO $ print (pretty (implGrChc g'))
      (`applyModel` g') <$> Z3.solveChc (implGrChc g')

-- | Convert the forward edges of the graph into a system of Constrained Horn Clauses.
implGrChc :: Graph Idx Form Inst -> [Chc]
implGrChc g = map rule topConns
  where
    topConns = -- to find the graph connections in topological order...
      (g & G.itopEdge                                  -- for each edge...
            (\is e -> Identity (G.omap inspect is, e)) -- lookup the edge indexes
         & fromJust                                    -- we know the graph has no backedges
         & runIdentity) ^.. G.iallEdges                -- collect all the connections
      where
        inspect i = (i, g ^?! ix i)

    -- each hypergraph connection converts to a Horn Clause.
    rule (G.HEdge lhs (i, v), f) =
      let lhs' = map buildRel (S.toList lhs)
      in case lengthOf (G.iedgesFrom i) g of
        -- If the target vertex has no successors, then it's a query
        0 -> Query lhs' f ((v ^. instForm) & vars %~ aliased f)
        -- Otherwise, the vertex is part of a rule.
        _ -> Rule  lhs' f (buildRel (i, v & vars %~ aliased f))

    aliased f v =
      let aliasedSet = concatMap (\(n, _) -> case n of
            FreeV n l True -> [n]
            _ -> []) (f ^.. vars . _Free)
      in case v of
           Free (FreeV n l b) t -> if n `elem` aliasedSet
                                   then Free (FreeV n l True) t
                                   else Free (FreeV n l False) t
           Bound n t -> Bound n t
           -- NoAlias n -> if n `elem` aliasedSet then Aliased n else NoAlias n

    -- construct an applied predicate from the instance
    buildRel (i, v) =
      mkApp ("r" ++ show i) (v ^. instVars)

-- | Augment the fact at each vertex in the graph by the fact in the model.
applyModel :: Model -> Graph Idx Form Inst -> Graph Idx Form Inst
applyModel model = G.imapVert applyInst
  where
    applyInst i v =
      v & instForm %~ (\f ->
          M.findWithDefault f i instMap -- replace the formula by the value in the map
        & instantiate (v ^. instVars))  -- replace the bound variables by the instance variables

    instMap = getModel model
      & M.filterWithKey (\k _ -> head (varName k) == 'r') -- only consider the instance predicates
      & M.mapKeys (read . head . splitOn "/" . tail . varName)                 -- convert the keys of the map to indexes
