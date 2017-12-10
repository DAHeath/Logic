module Logic.ImplicationGraph.Safety where

import           Control.Monad.State

import           Data.Optic.Directed.HyperGraph (Graph)

import           Logic.Var
import           Logic.Model
import           Logic.Formula
import           Logic.ImplicationGraph.Accessors
import           Logic.ImplicationGraph.Induction
import           Logic.ImplicationGraph.Types

-- | Repeatedly unwind the program until a counterexample is found or inductive
-- invariants are found.
solve :: MonadIO m => Form -> Graph Loc Edge Inst -> m (Either Model ImplGr)
solve q g = loop (fromGraph (query q g))
