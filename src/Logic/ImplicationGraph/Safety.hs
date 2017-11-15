module Logic.ImplicationGraph.Safety where

import           Control.Lens
import           Control.Monad.State

import           Data.Optic.Graph (Graph)
import qualified Data.Optic.Graph as G

import           Logic.Model
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Chc
import           Logic.ImplicationGraph.Induction

-- | Repeatedly unwind the program until a counterexample is found or inductive
-- invariants are found.
solve :: (AsInteger i, MonadIO m) => Graph i Edge Vert -> HyperEdges -> m (Either Model (ImplGr Edge))
solve g hs =
  case fromGraph g hs of
    Nothing -> error "bad safety graph"
    Just g' -> loop safetyStrat g'

safetyStrat :: Strategy Edge
safetyStrat =
  let theStrat = Strategy
        { backs = G.backEdges
        , interp = interpolate
        , predInd = \g i -> (: []) <$> allInd (predInd theStrat) g i (G.predecessors i (g ^. implGr))
        }
  in theStrat
