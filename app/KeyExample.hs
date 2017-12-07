{-# LANGUAGE QuasiQuotes #-}
import           Control.Lens

import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G
import qualified Data.Optic.Graph.Extras as G
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Text.Prettyprint.Doc

import           Logic.Var
import           Logic.Name
import           Logic.Formula
import           Logic.Formula.Parser
import qualified Logic.Type as T
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Equivalence

a1 = Free (NoAlias (Located 1 ["a"])) T.Int
r1 = Free (NoAlias (Located 1 ["r"])) T.Int
a2 = Free (NoAlias (Located 2 ["a"])) T.Int
r2 = Free (NoAlias (Located 2 ["r"])) T.Int

rec :: Graph Loc (Form BasicName) (Inst BasicName)
rec = G.fromLists
  [ (Loc 0, emptyInst (Loc 0) [])
  , (Loc 1, emptyInst (Loc 1) [a1, r1])
  , (Loc 2, emptyInst (Loc 2) [a2, r2])
  ]
  [ (G.HEdge (S.singleton (Loc 0)) (Loc 1), [form|#v1/a:Int <= 0
                                               && #v1/r:Int = 0|])
  , (G.HEdge (S.fromList [Loc 0, Loc 1]) (Loc 1), [form|#v1/a:Int > 0
                                                     &&  v1/a:Int = #v1/a:Int - 1
                                                     && #v1/r:Int = #v1/a:Int + v1/r:Int|])
  , (G.HEdge (S.singleton (Loc 1)) (Loc 2), [form|#v2/a:Int = v1/a:Int
                                               && #v2/r:Int = v1/r:Int|])
  ]

x1 = Free (NoAlias (Located 1 ["x"])) T.Int
s1 = Free (NoAlias (Located 1 ["s"])) T.Int
p1 = Free (NoAlias (Located 1 ["p"])) T.Int
s2 = Free (NoAlias (Located 2 ["s"])) T.Int
p2 = Free (NoAlias (Located 2 ["p"])) T.Int

loop :: Graph Loc (Form BasicName) (Inst BasicName)
loop = G.fromLists
  [ (Loc 0, emptyInst (Loc 0) [])
  , (Loc 1, emptyInst (Loc 1) [p1, x1, s1])
  , (Loc 2, emptyInst (Loc 2) [p2, s2])
  ]
  [ (G.HEdge (S.singleton (Loc 0)) (Loc 1), [form|#v1/p:Int = #v1/x:Int
                                               && #v1/s:Int = 0|])
  , (G.HEdge (S.singleton (Loc 1)) (Loc 1), [form| v1/x:Int > 0
                                               && #v1/p:Int = v1/p:Int
                                               && #v1/s:Int = v1/s:Int + v1/x:Int
                                               && #v1/x:Int = v1/x:Int - 1 |])
  , (G.HEdge (S.singleton (Loc 1)) (Loc 2), [form| v1/x:Int <= 0
                                               && #v2/p:Int = v1/p:Int
                                               && #v2/s:Int = v1/s:Int |])
  ]

main :: IO ()
main = do
  G.display "rec" rec
  G.display "loop" loop
  sol <- solve (Loc 2) (Loc 2)
    [form|v2/a:Int = v2/p:Int -> v2/r:Int = v2/s:Int|] rec loop
  case sol of
    Left e -> print (pretty e)
    Right m ->
      G.display "sol" m
