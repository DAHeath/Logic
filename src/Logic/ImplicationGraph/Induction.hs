{-# LANGUAGE TypeFamilies #-}
module Logic.ImplicationGraph.Induction where

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Monad.Loops (anyM)

import           Data.Optic.Directed.Graph (Graph)
import qualified Data.Optic.Directed.Graph as G
import qualified Data.Optic.Graph.Extras as G
import           Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Maybe (mapMaybe, fromMaybe)
import           Data.Text.Prettyprint.Doc

import           Logic.Formula
import           Logic.Model
import qualified Logic.Solver.Z3 as Z3
import           Logic.ImplicationGraph

type PredInd e m = ImplGr e -> Idx -> m [Bool]

data Strategy e = Strategy
    -- What constitutes a back edge for the strategy?
  { backs :: Graph Idx e Vert -> [(G.Pair Idx, e)]
    -- How is interpolation performed over the graph?
  , interp :: forall m. MonadIO m => ImplGr e -> m (Either Model (ImplGr e))
    -- How do we know if the predecessors indicate the current vertex is inductive?
  , predInd :: forall m. (MonadIO m, MonadState (Map Idx Bool) m) => PredInd e m
  }

-- | Check whether the vertex labels in the graph form an inductive relationship.
inductive :: MonadIO m => PredInd e (StateT (Map Idx Bool) m) -> ImplGr e -> m (Map Idx Bool)
inductive pc g = execStateT (ind pc g (g ^. exit)) M.empty

ind :: (MonadIO m, MonadState (Map Idx Bool) m) => PredInd e m -> ImplGr e -> Idx -> m Bool
ind pc g i = maybe (computeInd pc g i) return . M.lookup i =<< get

indPred :: (MonadIO m, MonadState (Map Idx Bool) m)
        => PredInd e m -> ImplGr e -> Idx -> Idx -> m Bool
indPred pc g i i' = if i >= i' then return False else ind pc g i'

computeInd :: (MonadIO m, MonadState (Map Idx Bool) m)
           => PredInd e m -> ImplGr e -> Idx -> m Bool
computeInd pc g i =
  (at i <?=) =<< maybe (return False) (\v -> do
    psInd <- pc g i
    case v of
      QueryV _ -> return (or psInd)
      InstanceV loc _ f ->
        or <$> sequence ([ return $ f == LBool True
                         , anyM (`Z3.entails` f) (descendantInstanceVs g loc i)
                         ] ++ map return psInd)) (g ^. at i)

allInd :: (MonadIO m, MonadState (Map Idx Bool) m)
       => PredInd e m -> ImplGr e -> Idx -> [Idx] -> m Bool
allInd pc g i is = and <$> mapM (indPred pc g i) is

descendantInstanceVs :: ImplGr e -> Loc -> Idx -> [Form]
descendantInstanceVs g loc i =
  G.descendants i (g ^. implGr)
    & S.toList
    & filter (\i' -> case g ^? implGr . ix i' . _InstanceV . _1 of
      Nothing -> False
      Just loc' -> i /= i' && loc == loc')
    & mapMaybe (\i' -> g ^? ix i' . _InstanceV . _3)

-- | Apply the strategy to the graph until a either a counterxample or an inductive
-- solution is found.
loop :: (MonadIO m, Pretty e)
     => Strategy e
     -> ImplGr e -> m (Either Model (ImplGr e))
loop strat g = do
  solved <- runSolve $ loop' g
  case solved of
    Left (Failed m) -> return (Left m)
    Left (Complete res) -> return (Right res)
    Right _ -> error "infinite loop terminated successfully?"
  where
    loop' gr = loop' =<< step strat gr

-- | Perform a step of the unwinding by
-- 1. interpolating over the current graph
-- 2. checking if the solution is inductive (and terminating if it is)
-- 3. unwinding the graph over all backedges
step :: (Pretty e, Solve e m) => Strategy e -> ImplGr e -> m (ImplGr e)
step strat g = do
  G.display "step" (g ^. implGr)
  interp strat g >>= either (throwError . Failed) (\interp -> do
    liftIO getLine
    let end = g ^. exit
    indM <- inductive (predInd strat) interp
    let isInd = M.keys $ M.filter id indM
    when (M.lookup end indM == Just True) $ throwError $ Complete interp
    return $ unwindAll (backs strat (g ^. implGr)) isInd end interp)
