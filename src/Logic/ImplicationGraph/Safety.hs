module Logic.ImplicationGraph.Safety where

import           Control.Lens
import           Control.Monad.State

import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G
import qualified Data.Set as S

import           Logic.Model
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Chc
import           Logic.ImplicationGraph.Induction

-- | Repeatedly unwind the program until a counterexample is found or inductive
-- invariants are found.
solve :: (AsInteger i, MonadIO m) => Graph i Edge Vert -> m (Either Model (ImplGr Edge))
solve g = loop safetyStrat (fromGraph g)

safetyStrat :: Strategy Edge
safetyStrat =
  let theStrat = Strategy
        { backs = revBackEdges
        , interp = interpolate
        , predInd = \g i -> (: []) <$> allInd (predInd theStrat) g i
                              (S.toList $ G.predecessors g i)
        }
  in theStrat
