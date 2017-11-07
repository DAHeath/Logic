module Logic.ImplicationGraph.Induction where

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Loops (anyM)

import           Data.Optic.Graph (Graph)
import qualified Data.Optic.Graph as G
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (mapMaybe)

import           Logic.Formula
import qualified Logic.Solver.Z3 as Z3
import           Logic.ImplicationGraph

type PredComp e m = Graph Idx e Vert -> Idx -> m [Bool]

-- | Check whether the vertex labels in the graph form an inductive relationship.
inductive' :: MonadIO m => PredComp e (StateT (Map Idx Bool) m)
           -> Idx -> Graph Idx e Vert -> m (Map Idx Bool)
inductive' pc start g = execStateT (ind pc g start) M.empty

ind :: (MonadIO m, MonadState (Map Idx Bool) m)
    => PredComp e m -> Graph Idx e Vert -> Idx -> m Bool
ind pc g i = maybe (computeInd pc g i) return . M.lookup i =<< get

indPred :: (MonadIO m, MonadState (Map Idx Bool) m)
        => PredComp e m -> Graph Idx e Vert -> Idx -> Idx -> m Bool
indPred pc g i i' = if i <= i' then return False else ind pc g i'

computeInd :: (MonadIO m, MonadState (Map Idx Bool) m)
           => PredComp e m -> Graph Idx e Vert -> Idx -> m Bool
computeInd pc g i =
  (at i <?=) =<< maybe (return False) (\v -> do
    psInd <- pc g i
    case v of
      QueryV _ -> return (or psInd)
      InductiveV{}  -> return True
      InstanceV _ f ->
        or <$> sequence ([ return $ f == LBool True
                         , anyM (`Z3.entails` f) (descendantInstanceVs g i)
                         ] ++ map return psInd)) (g ^. at i)

allInd :: (MonadIO m, MonadState (Map Idx Bool) m)
       => PredComp e m -> Graph Idx e Vert -> Idx -> [Idx] -> m Bool
allInd pc g i is = and <$> mapM (indPred pc g i) is

descendantInstanceVs :: Graph Idx e Vert -> Idx -> [Form]
descendantInstanceVs g i =
  G.descendants i g
    & filter (match i)
    & filter (/= i)
    & mapMaybe (\i' -> g ^? ix i' . _InstanceV . _2)
