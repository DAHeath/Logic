{-# LANGUAGE TypeFamilies #-}
module Logic.ImplicationGraph.Induction where

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Monad.Loops (anyM)

import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G
import qualified Data.Optic.Graph.Extras as G
import           Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Maybe (mapMaybe)
import           Data.Text.Prettyprint.Doc

import           Logic.Formula
import           Logic.Model
import qualified Logic.Solver.Z3 as Z3
import           Logic.ImplicationGraph

type PredInd e m = ImplGr e -> Idx -> m [Bool]

data Strategy e = Strategy
    -- What constitutes a back edge for the strategy?
  { backs :: Graph Idx e Inst -> [(G.HEdge Idx, e)]
    -- How is interpolation performed over the graph?
  , interp :: forall m. MonadIO m => ImplGr e -> m (Either Model (ImplGr e))
    -- How do we know if the predecessors indicate the current vertex is inductive?
  , predInd :: forall m. (MonadIO m, MonadState (Map Idx Bool) m) => PredInd e m
  }

-- | Check whether the vertex labels in the graph form an inductive relationship.
inductive :: MonadIO m => Idx -> PredInd e (StateT (Map Idx Bool) m) -> ImplGr e -> m (Map Idx Bool)
inductive end pc g = execStateT (ind pc g end) M.empty

ind :: (MonadIO m, MonadState (Map Idx Bool) m) => PredInd e m -> ImplGr e -> Idx -> m Bool
ind pc g i = maybe (computeInd pc g i) return . M.lookup i =<< get

indPred :: (MonadIO m, MonadState (Map Idx Bool) m)
        => PredInd e m -> ImplGr e -> Idx -> Idx -> m Bool
indPred pc g i i' = if i <= i' then return False else ind pc g i'

computeInd :: (MonadIO m, MonadState (Map Idx Bool) m)
           => PredInd e m -> ImplGr e -> Idx -> m Bool
computeInd pc g i =
  (at i <?=) =<< maybe (return False) (\v -> do
    psInd <- pc g i
    case v of
      Inst loc _ f ->
        or <$> sequence ([ return $ f == LBool True
                         , anyM (`Z3.entails` f) (descendantInstanceVs g loc i)
                         ] ++ map return psInd)) (g ^. at i)

allInd :: (MonadIO m, MonadState (Map Idx Bool) m)
       => PredInd e m -> ImplGr e -> Idx -> [Idx] -> m Bool
allInd pc g i is = and <$> mapM (indPred pc g i) is

descendantInstanceVs :: ImplGr e -> Loc -> Idx -> [Form]
descendantInstanceVs g loc i =
  G.descendants i g
    & S.toList
    & filter (\i' -> case g ^? ix i' . instLoc of
      Nothing -> False
      Just loc' -> i /= i' && loc == loc')
    & mapMaybe (\i' -> g ^? ix i' . instForm)

-- | Apply the strategy to the graph until a either a counterxample or an inductive
-- solution is found.
loop :: (MonadIO m, Pretty e, Show e)
     => Strategy e
     -> ImplGr e -> m (Either Model (ImplGr e))
loop strat g = do
  solved <- runExceptT $ loop' g
  case solved of
    Left (Failed m) -> return (Left m)
    Left (Complete res) -> return (Right res)
    Right _ -> error "infinite loop terminated successfully?"
  where
    loop' gr = loop' =<< step end strat gr
    end = head $ filter (\i -> lengthOf (G.edgesFrom i) g == 0) (G.idxs g)

-- | Perform a step of the unwinding by
-- 1. interpolating over the current graph
-- 2. checking if the solution is inductive (and terminating if it is)
-- 3. unwinding the graph over all backedges
step :: (Pretty e, MonadError (Result e) m, MonadIO m)
     => Idx -> Strategy e -> ImplGr e -> m (ImplGr e)
step end strat g = do
  G.display "step" g
  interp strat g >>= either (throwError . Failed) (\itp -> do
    _ <- liftIO getLine
    indM <- inductive end (predInd strat) itp
    let isInd = M.keys $ M.filter id indM
    when (M.lookup end indM == Just True) $ throwError $ Complete itp
    return $ unwindAll (backs strat g) isInd end itp)
