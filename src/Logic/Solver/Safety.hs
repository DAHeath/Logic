module Logic.Solver.Safety where

import           Control.Monad.State

import           Data.Optic.Directed.HyperGraph (Graph)

import           Logic.Formula
import           Logic.ImplicationGraph

-- | Repeatedly unwind the program until a counterexample is found or inductive
-- invariants are found.
solve :: MonadIO m => Form -> Graph Loc Edge Inst -> m (Either Model ImplGr)
solve q = loop . fromGraph . query q
