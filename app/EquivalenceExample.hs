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

r0  = Var ["r"] 0 False T.Int
n0  = Var ["n"] 0 False T.Int

m0  = Var ["m"] 0 False T.Int
x0  = Var ["x"] 0 False T.Int
m1  = Var ["m"] 1 False T.Int
x1  = Var ["x"] 1 False T.Int

ad0 :: Graph Loc Form Inst
ad0 = G.fromLists
  [ (Loc 0, emptyInst (Loc 0) [n0, r0]) ]
  [ (G.HEdge S.empty (Loc 0), [form|#r:Int = #n:Int - 9 * ((#n:Int - 1) / 9)|]) ]

ad1 :: Graph Loc Form Inst
ad1 = G.fromLists
  [ (Loc 0, emptyInst (Loc 0) [m0, x0])
  , (Loc 1, emptyInst (Loc 1) [m1, x1])
  ]
  [ (G.HEdge S.empty (Loc 0), [form|#x/0:Int = #m/0:Int|])
  , (G.HEdge (S.singleton (Loc 0)) (Loc 0), [form| x/0:Int > 9
                                                && #x/0:Int = x/0:Int / 10 + x/0:Int % 10
                                                && #m/0:Int = m/0:Int|])
  , (G.HEdge (S.singleton (Loc 0)) (Loc 1), [form|x/0:Int <= 9
                                                && #x/1:Int = x/0:Int
                                                && #m/1:Int = m/0:Int |])
  ]

main :: IO ()
main = do
  sol <- solve
    [form|n:Int > 0 && n:Int = m/1:Int -> x/1:Int = r:Int|] ad0 ad1
  case sol of
    Left e -> print (pretty e)
    Right m ->
      G.display "sol" m
