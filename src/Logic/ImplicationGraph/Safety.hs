module Logic.ImplicationGraph.Safety where

import           Control.Lens
import           Control.Monad.State

import           Data.Optic.Graph (Graph)
import qualified Data.Optic.Graph as G

import           Logic.Model
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Induction

-- | Repeatedly unwind the program until a counterexample is found or inductive
-- invariants are found.
solve :: (IntoIdx i, MonadIO m) => ImplGr i Edge -> m (Either Model (ImplGr Idx Edge))
solve = loop safetyStrat

safetyStrat :: Strategy Edge
safetyStrat =
  let theStrat = Strategy
        { backs = G.backEdges
        , interp = interpolate
        , predInd = \g i -> (: []) <$> allInd (predInd theStrat) g i (G.predecessors i (g ^. implGr))
        }
  in theStrat
