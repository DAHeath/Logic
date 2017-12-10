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

import           Language.Structured

r, n, m, x :: Var
r = Var ["r"] 0 False T.Int
n = Var ["n"] 0 False T.Int
m = Var ["m"] 0 False T.Int
x = Var ["x"] 0 False T.Int

ad0 :: Graph Loc Edge Inst
ad0 = singleNonRec
  [ (r := [form|n:Int - 9 * ((n:Int - 1) / 9)|], [r, n]) ]

ad1 :: Graph Loc Edge Inst
ad1 = singleNonRec
  [ (x := [form|m:Int|], [x, m])
  , (While [form|x:Int > 9|]
      [ (x := [form|x:Int / 10 + x:Int % 10|], [x, m]) ], [x, m])
  ]

main :: IO ()
main = do
  sol <- solve
    [form|n/1:Int > 0 && n/1:Int = m/1:Int -> x/1:Int = r/1:Int|] ad0 ad1
  case sol of
    Left e -> print (pretty e)
    Right m ->
      G.display "sol" m
