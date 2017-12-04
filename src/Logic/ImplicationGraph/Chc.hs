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

import           Logic.Formula
import           Logic.Model
import           Logic.Var
import           Logic.Name
import           Logic.Chc
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.LTree
import qualified Logic.Solver.Z3 as Z3

-- | Interpolate the facts in the graph using CHC solving to label the vertices
-- with fresh definitions.
interpolate :: (Name n, MonadError (Model (Aliasable n)) m, MonadIO m)
            => ImplGr (Aliasable n) -> m (ImplGr (Aliasable n))
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
implGrChc :: forall n. Name n => Graph Idx (Form (Aliasable n)) (Inst (Aliasable n)) -> [Chc (Aliasable n)]
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
        0 -> Query lhs' f ((v ^. instForm) & vars' %~ fmap (aliased f))
        -- Otherwise, the vertex is part of a rule.
        _ -> Rule  lhs' f (buildRel (i, v & vars' %~ fmap (aliased f)))

    vars' :: Data a => Traversal' a (Var (Aliasable n))
    vars' = vars

    aliased f v =
      let aliasedSet = concatMap (\(n, _) -> case n of
            Aliased n -> [n]
            NoAlias _ -> []) (f ^.. vars . _Free)
      in case v of
           Aliased n -> Aliased n
           NoAlias n -> if n `elem` aliasedSet then Aliased n else NoAlias n

    -- construct an applied predicate from the instance
    buildRel (i, v) =
      let s = "v0/r" ++ _Show # i
      in mkApp (fromJust $ s ^? name) (v ^. instVars)

-- | Augment the fact at each vertex in the graph by the fact in the model.
applyModel :: Name n => Model n -> Graph Idx (Form n) (Inst n) -> Graph Idx (Form n) (Inst n)
applyModel model = G.imapVert applyInst
  where
    applyInst i v =
      v & instForm %~ (\f ->
          M.findWithDefault f i instMap -- replace the formula by the value in the map
        & instantiate (v ^. instVars))  -- replace the bound variables by the instance variables

    instMap = getModel model
      & M.filterWithKey (\k _ -> head (varName k) == 'v'
                              && length (varName k) >= 4
                              && varName k !! 3 == 'r')   -- only consider the instance predicates
      & M.mapKeys (read . drop 4 . varName)               -- convert the keys of the map to indexes

