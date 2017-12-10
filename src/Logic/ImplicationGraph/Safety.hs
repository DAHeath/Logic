module Logic.ImplicationGraph.Safety where

import           Control.Monad.State

import           Data.Optic.Directed.HyperGraph (Graph)

import           Logic.Model
import           Logic.ImplicationGraph.Accessors
import           Logic.ImplicationGraph.Induction
import           Logic.ImplicationGraph.Types

-- | Repeatedly unwind the program until a counterexample is found or inductive
-- invariants are found.
solve :: (Ord i, MonadIO m) => Graph i Edge Inst -> m (Either Model ImplGr)
solve = loop . fromGraph
