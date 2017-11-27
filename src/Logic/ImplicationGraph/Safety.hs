module Logic.ImplicationGraph.Safety where

import           Control.Lens
import           Control.Monad.State

import           Data.Optic.Directed.Graph (Graph)
import qualified Data.Optic.Directed.Graph as G
import qualified Data.Set as S

import           Logic.Model
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Chc
import           Logic.ImplicationGraph.Induction

-- | Repeatedly unwind the program until a counterexample is found or inductive
-- invariants are found.
solve :: (AsInteger i, MonadIO m) => Graph i Edge Vert -> HyperEdges -> m (Either Model (ImplGr Edge))
solve g hs =
  case fromGraph hs g of
    Nothing -> error "bad safety graph"
    Just g' -> loop safetyStrat g'

safetyStrat :: Strategy Edge
safetyStrat =
  let theStrat = Strategy
        { backs = revBackEdges
        , interp = interpolate
        , predInd = \g i -> (: []) <$> allInd (predInd theStrat) g i
                              (S.toList $ G.predecessors (g ^. implGr) i)
        }
  in theStrat
