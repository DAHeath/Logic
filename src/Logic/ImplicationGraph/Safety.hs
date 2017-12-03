module Logic.ImplicationGraph.Safety where

import           Control.Monad.State

import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G

import           Logic.Model
import           Logic.Var
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Induction
import           Logic.ImplicationGraph.LTree
import           Logic.ImplicationGraph.Simplify

-- | Repeatedly unwind the program until a counterexample is found or inductive
-- invariants are found.
solve :: (Name n, Ord i, MonadIO m)
      => Graph i (Edge n) (Inst n) -> m (Either (Model n) (ImplGr n))
solve = loop . G.mapEdge Leaf . fromGraph
-- solve = loop . fromGraph
