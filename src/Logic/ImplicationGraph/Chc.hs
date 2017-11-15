module Logic.ImplicationGraph.Chc where

import           Control.Lens
import           Control.Monad.State

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Optic.Graph (Graph)
import qualified Data.Optic.Graph as G
import           Data.Maybe (mapMaybe)
import           Data.Text.Prettyprint.Doc

import           Logic.Model
import           Logic.Var
import           Logic.Chc
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Simplify (conjunction)
import qualified Logic.Solver.Z3 as Z3

-- | Convert the graph into a system of Constrained Horn Clauses.
implGrChc :: ImplGr Edge -> [Chc]
implGrChc g = concatMap idxRules (G.idxs (g ^. implGr))
  where
    idxApp i = instApp i =<< g ^? ix i . _InstanceV
    instApp _ ([], _) = Nothing
    instApp i (vs, _) = Just $ mkApp ('r' : written # i) vs

    idxRule i f rhs = vertRule i f rhs <$> g ^? ix i
    vertRule i f rhs = \case
      InstanceV _ _ | i == g ^. entrance -> Rule [] f rhs
      InstanceV vs _   -> Rule [mkApp ('r':written # i) vs] f rhs
      QueryV _         -> undefined

    idxRules i = maybe [] (\case
      InstanceV _ _ ->
        mapMaybe (\(i', Edge f mvs) -> do
          rhs <- subst mvs <$> idxApp i
          idxRule i' f rhs) (singleIncoming i)
        ++
        mapMaybe (\(i1, i2, Edge f mvs) -> do
          rhs <- subst mvs <$> idxApp i
          r1 <- idxApp i1
          r2 <- idxApp i2
          return $ Rule [r1, r2] f rhs) (hyperIncoming i)

      QueryV f -> queries i f) (g ^? ix i)

    queries i f =
      mapMaybe (\(i', Edge e mvs) -> do
        lhs <- idxApp i'
        let rhs = subst mvs f
        return (Query [lhs] e rhs)) (singleIncoming i)
        ++
      mapMaybe (\(i1, i2, Edge e mvs) -> do
        let rhs = subst mvs f
        r1 <- idxApp i1
        r2 <- idxApp i2
        return $ Query [r1, r2] e rhs) (hyperIncoming i)

    -- We only create rules for non-back edges
    relevantIncoming i = g ^@.. implGr . G.iedgesTo i . indices (i >)

    singleIncoming :: Idx -> [(Idx, Edge)]
    singleIncoming i =
      filter (\(i', _) -> notElemOf (traverse.both) (i' ^. idxIden) (hyperIdxs i))
             (relevantIncoming i)

    hyperIncoming :: Idx -> [(Idx, Idx, Edge)]
    hyperIncoming i = map (\(i1, i2) ->
      let (ix1, e1) = head $ filter (\(ix, _) -> ix ^. idxIden == i1) (relevantIncoming i)
          (ix2, e2) = head $ filter (\(ix, _) -> ix ^. idxIden == i2) (relevantIncoming i)
      in (ix1, ix2, conjunction e1 e2)) (hyperIdxs i)

    hyperIdxs :: Idx -> [(Integer, Integer)]
    hyperIdxs i = M.findWithDefault [] (i ^. idxIden) (g ^. hyperEdges)

-- | Interpolate the facts in the graph using CHC solving to label the vertices
-- with fresh definitions.
interpolate :: MonadIO m => ImplGr Edge -> m (Either Model (ImplGr Edge))
interpolate g = do
  liftIO $ print $ pretty (implGrChc g)
  (fmap . fmap) (`applyModel` g) (Z3.solveChc (implGrChc g))
