module Logic.ImplicationGraph.Safety where

import           Control.Monad.State
import           Control.Monad.Except

import qualified Data.Optic.Graph as G
import qualified Data.Optic.Graph.Extras as G
import qualified Data.Map as M
import           Data.Map (Map)

import           Logic.Model
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Induction

-- | Repeatedly unwind the program until a counterexample is found or inductive
-- invariants are found.
solve :: MonadIO m => Integer -> ImplGr Integer -> m (Either Model (ImplGr Idx))
solve = loop safetyStrat

safetyStrat :: Strategy Edge
safetyStrat =
  let theStrat = Strategy
        { backs = G.backEdges
        , interp = interpolate
        , predInd = \g i -> (: []) <$> allInd (predInd theStrat) g i (G.predecessors i g)
        }
  in theStrat
