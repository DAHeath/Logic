module Logic.Solver.Safety where

import           Control.Monad.State

import           Data.Functor.Identity
import           Data.Copointed
import           Data.Loc
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G

import           Logic.Formula
import           Logic.ImplicationGraph

-- | Repeatedly unwind the program until a counterexample is found or inductive
-- invariants are found.
solve :: (MonadIO m, Copointed e1)
      => Form -> Graph Loc (e1 Form) Inst -> m (Either Model (ImplGr Identity))
solve q = loop . fromGraph . query q . G.mapEdges (Identity . copoint)
