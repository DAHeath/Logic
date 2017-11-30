module Logic.ImplicationGraph.Safety where

import           Control.Monad.State

import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G

import           Logic.Model
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Induction
import           Logic.ImplicationGraph.LTree

-- | Repeatedly unwind the program until a counterexample is found or inductive
-- invariants are found.
solve :: (Ord i, MonadIO m) => Graph i Edge Inst -> m (Either Model ImplGr)
solve = loop . G.mapEdge Leaf . fromGraph
