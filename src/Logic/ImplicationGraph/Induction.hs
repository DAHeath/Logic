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
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Maybe (mapMaybe)
import           Data.Text.Prettyprint.Doc

import           Logic.Formula
import           Logic.Model
import qualified Logic.Solver.Z3 as Z3
import           Logic.ImplicationGraph

import           Prelude hiding (pi)

type PredInd e m = ImplGr e -> Idx -> m [Bool]

data Strategy e = Strategy
    -- What constitutes a back edge for the strategy?
  { backs :: Graph Idx e Inst -> [(G.HEdge Idx, e)]
    -- How is interpolation performed over the graph?
  , interp :: forall m. (MonadIO m, MonadError Model m) => ImplGr e -> m (ImplGr e)
    -- How do we know if the predecessors indicate the current vertex is inductive?
  , predInd :: forall m. (MonadIO m, MonadState (Map Idx Bool) m) => PredInd e m
  }

-- | Find the vertex labels in the graph which are inductive.
inductive :: MonadIO m => PredInd e (StateT (Map Idx Bool) m) -> ImplGr e -> m (Set Idx)
inductive pi g = M.keysSet . M.filter id <$> execStateT (ind pi g (end g)) M.empty

-- | Decide if the given index
ind :: (MonadIO m, MonadState (Map Idx Bool) m) => PredInd e m -> ImplGr e -> Idx -> m Bool
ind pi g i =
  maybe
    (computeInd pi g i)  -- compute inductiveness when we don't know the answer
    return               -- if we memoized the answer, we're done
    . M.lookup i =<< get -- lookup the answer from the state

indPred :: (MonadIO m, MonadState (Map Idx Bool) m)
        => PredInd e m -> ImplGr e -> Idx -> Idx -> m Bool
indPred pi g i i' =
  if i <= i'        -- if we check the 'predecessor' and it occurs after the current index (back edge)
  then return False -- then it is automatically not inductive
  else ind pi g i'  -- otherwise, we recurse

computeInd :: (MonadIO m, MonadState (Map Idx Bool) m)
           => PredInd e m -> ImplGr e -> Idx -> m Bool
computeInd pi g i =
  (at i <?=) =<< -- find the answer and update the memoization table
    maybe
      (return False)    -- if there is no vertex, it is not inductive
      (\(Inst loc _ f) -> do
        psInd <- pi g i -- check inductiveness via predecessors
        or <$> sequence (                                   -- this index is inductive if...
          [ return $ f == LBool True                        -- it is trivially inductive
          , anyM (`Z3.entails` f) (descendantForms g loc i) -- a descendant at the same location entails it
          ] ++ map return psInd)) (g ^. at i)               -- it's inductive via its predecessors

-- | Are all predecessors inductive?
allInd :: (MonadIO m, MonadState (Map Idx Bool) m)
       => PredInd e m -> ImplGr e -> Idx -> [Idx] -> m Bool
allInd pi g i is = and <$> mapM (indPred pi g i) is

-- | Find the formulas of descendants at the same location.
descendantForms :: ImplGr e -> Loc -> Idx -> [Form]
descendantForms g loc i =
  G.descendants i g                      -- look at all descendants
    & S.delete i                         -- an instance cannot entail itself
    & S.toList                           -- convert to a list
    & mapMaybe (\i' -> g ^? ix i')       -- lookup the vertex at each index
    & filter (\v -> v ^. instLoc == loc) -- only consider those at the location in question
    & map _instForm                      -- fetch the formula

-- | Find the end (query) of the graph
end :: ImplGr e -> Idx
end g = head $ filter (\i -> lengthOf (G.edgesFrom i) g == 0) (G.idxs g) -- the query has no outgoing edges

-- | Apply the strategy to the graph until a either a counterxample or an inductive
-- solution is found.  Perform a step of the unwinding by
-- 1. interpolating over the current graph
-- 2. checking if the solution is inductive (and terminating if it is)
-- 3. unwinding the graph over all backedges
loop :: (MonadIO m, Pretty e, Show e)
     => Strategy e -> ImplGr e -> m (Either Model (ImplGr e))
loop strat = runExceptT . loop'
  where
    loop' g = do
      G.display "step" g
      _ <- liftIO getLine
      itp <- interp strat g                                   -- interpolate
      indS <- inductive (predInd strat) itp                   -- check inductiveness
      if end g `elem` indS                                    -- if the query is inductive...
      then return itp                                         -- we're done
      else loop' (unwindAll (backs strat g) indS (end g) itp) -- otherwise unwind and repeat
