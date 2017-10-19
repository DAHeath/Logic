{-# LANGUAGE QuasiQuotes #-}

import           Control.Monad (void)
import           Control.Monad.State
import           Control.Monad.Except

import qualified Data.Ord.Graph as G
import qualified Data.Ord.Graph.Extras as G
import qualified Data.Map as M

import qualified Logic.Type as T
import           Logic.Formula.Parser
import           Logic.Var
import           Logic.ImplicationGraph.Type
import           Logic.ImplicationGraph.Equivalence
import           Logic.ImplicationGraph.Solve

g :: ImplGr
g = G.fromLists
  [ ((0, 0), InstanceNode $ emptyInstance [])
  , ((1, 0), InstanceNode $ emptyInstance [])
  , ((2, 0), InstanceNode $ emptyInstance [])
  ]
  [ ((0, 0), (1, 0), ImplGrEdge [form|true|] M.empty)
  , ((1, 0), (1, 0), ImplGrEdge [form|true|] M.empty)
  , ((1, 0), (2, 0), ImplGrEdge [form|true|] M.empty)
  ]

main :: IO ()
main = do
  sol <- evalStateT (runExceptT (do
    g' <- orWiseProduct g g
    unfold (head $ backEdges' g') g'
    )) (mapSolveState (PLbl 0 0 0) $ emptySolveState g)
  case sol of
    Left e -> error "huh?"
    Right g' -> G.display "equiv" g'
