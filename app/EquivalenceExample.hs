{-# LANGUAGE QuasiQuotes #-}
import           Control.Lens

import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G
import qualified Data.Optic.Graph.Extras as G
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Text.Prettyprint.Doc

import           Logic.Var
import           Logic.Formula
import           Logic.Formula.Parser
import qualified Logic.Type as T
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Equivalence
import           Logic.ImplicationGraph.LTree
import           Logic.ImplicationGraph.Simplify

import Language.Structured

r0  = Var ["r"] 0 False T.Int
n0  = Var ["n"] 0 False T.Int

m0  = Var ["m"] 0 False T.Int
x0  = Var ["x"] 0 False T.Int
m1  = Var ["m"] 1 False T.Int
x1  = Var ["x"] 1 False T.Int

ad0 :: Program
ad0 = Program
  { _entryPoint = "f"
  , _procedures = M.singleton "f" ([], [],
    [ (r0 := [form|n:Int - 9 * ((n:Int - 1) / 9)|], [r0, n0]) ])
  }

ad1 :: Program
ad1 = Program
  { _entryPoint = "f"
  , _procedures = M.singleton "f" ([], [],
    [ (x0 := [form|m:Int|], [x0, m0])
    , (While [form|x:Int > 9|]
        [ (x0 := [form|x:Int / 10 + x:Int % 10|], [x0, m0]) ], [x0, m0])
    ])
  }

main :: IO ()
main = do
  sol <- solve
    [form|n/1:Int > 0 && n/1:Int = m/1:Int -> x/1:Int = r/1:Int|]
      (prune $ impGraph ad0)
      (prune $ impGraph ad1)
  case sol of
    Left e -> print (pretty e)
    Right m ->
      G.display "sol" m
