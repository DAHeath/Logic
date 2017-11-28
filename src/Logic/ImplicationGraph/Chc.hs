module Logic.ImplicationGraph.Chc where

import           Control.Lens
import           Control.Monad.State

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import           Data.List (sortBy)
import qualified Data.Set as S
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G
import           Data.Maybe (mapMaybe, fromJust)
import           Data.Text.Prettyprint.Doc

import           Logic.Model
import           Logic.Var
import           Logic.Chc
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Simplify (conjunction)
import qualified Logic.Solver.Z3 as Z3

-- | Convert the graph into a system of Constrained Horn Clauses.
implGrChc :: ImplGr Edge -> [Chc]
implGrChc g = organize $ map rule (G.connections (withoutRevBackEdges g))
  where
    organize :: [Chc] -> [Chc]
    organize = sortBy (\c1 c2 -> case (c1, c2) of
      (Query{}, Query{}) -> LT
      (Query{}, Rule{}) -> GT
      (Rule{}, Query{}) -> LT
      (Rule _ _ a1, Rule _ _ a2) ->
        compare (appNum a2) (appNum a1))

    appNum :: App -> Integer
    appNum = read . tail . varName . appOperator

    rule :: (G.HEdge (Idx, Vert), Edge) -> Chc
    rule (G.HEdge lhs (i, v), Edge f mvs) =
      let lhs' = mapMaybe (uncurry buildRel) (S.toList lhs)
      in case lengthOf (G.iedgesFrom i) g of
            0 -> Query lhs' f (subst mvs (v ^. vertForm))
            _ -> Rule lhs' f (subst mvs (fromJust $ buildRel i v))

    buildRel :: Idx -> Vert -> Maybe App
    buildRel i v = case v of
      Vert _ vs _ -> Just $ mkApp ('r' : _Show #i) vs

-- | Interpolate the facts in the graph using CHC solving to label the vertices
-- with fresh definitions.
interpolate :: MonadIO m => ImplGr Edge -> m (Either Model (ImplGr Edge))
interpolate g = do
  liftIO $ print $ pretty (implGrChc g)
  (fmap . fmap) (`applyModel` g) (Z3.solveChc (implGrChc g))
