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

a1 = Free (FreeV ["a"] 1 False) T.Int
r1 = Free (FreeV ["r"] 1 False) T.Int
a2 = Free (FreeV ["a"] 2 False) T.Int
r2 = Free (FreeV ["r"] 2 False) T.Int

rec :: Graph Loc Form Inst
rec = G.fromLists
  [ (Loc 0, emptyInst (Loc 0) [])
  , (Loc 1, emptyInst (Loc 1) [a1, r1])
  , (Loc 2, emptyInst (Loc 2) [a2, r2])
  ]
  [ (G.HEdge (S.singleton (Loc 0)) (Loc 1), [form|#a/1:Int <= 0
                                               && #r/1:Int = 0|])
  , (G.HEdge (S.fromList [Loc 0, Loc 1]) (Loc 1), [form|#a/1:Int > 0
                                                     &&  a/1:Int = #a/1:Int - 1
                                                     && #r/1:Int = #a/1:Int + r/1:Int|])
  , (G.HEdge (S.singleton (Loc 1)) (Loc 2), [form|#a/2:Int = a/1:Int
                                               && #r/2:Int = r/1:Int|])
  ]

x1 = Free (FreeV ["x"] 1 False) T.Int
s1 = Free (FreeV ["s"] 1 False) T.Int
p1 = Free (FreeV ["p"] 1 False) T.Int
s2 = Free (FreeV ["s"] 2 False) T.Int
p2 = Free (FreeV ["p"] 2 False) T.Int

loop :: Graph Loc Form Inst
loop = G.fromLists
  [ (Loc 0, emptyInst (Loc 0) [])
  , (Loc 1, emptyInst (Loc 1) [p1, x1, s1])
  , (Loc 2, emptyInst (Loc 2) [p2, s2])
  ]
  [ (G.HEdge (S.singleton (Loc 0)) (Loc 1), [form|#p/1:Int = #x/1:Int
                                               && #s/1:Int = 0|])
  , (G.HEdge (S.singleton (Loc 1)) (Loc 1), [form| x/1:Int > 0
                                               && #p/1:Int = p/1:Int
                                               && #s/1:Int = s/1:Int + x/1:Int
                                               && #x/1:Int = x/1:Int - 1 |])
  , (G.HEdge (S.singleton (Loc 1)) (Loc 2), [form| x/1:Int <= 0
                                               && #p/2:Int = p/1:Int
                                               && #s/2:Int = s/1:Int |])
  ]

main :: IO ()
main = do
  G.display "rec" rec
  G.display "loop" loop
  sol <- solve (Loc 2) (Loc 2)
    [form|a/2:Int = p/2:Int -> r/2:Int = s/2:Int|] rec loop
  case sol of
    Left e -> print (pretty e)
    Right m ->
      G.display "sol" m
