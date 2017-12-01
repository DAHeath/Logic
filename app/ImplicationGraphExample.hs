{-# LANGUAGE QuasiQuotes #-}
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G
import qualified Data.Optic.Graph.Extras as G
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Text.Prettyprint.Doc

import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Safety
import qualified Logic.Type as T
import           Logic.Formula.Parser
import           Logic.Var

main :: IO ()
main = do
  G.display "before.dot" example
  sol <- solve example
  case sol of
    Left m -> print (pretty m)
    Right r -> do
      G.display "test.dot" r
      print . pretty . M.toList =<< collectAnswer r

i, i', n :: Var
i  = Free ["i"] 0 T.Int
i' = Free ["i"] 1 T.Int
n  = Free ["n"] 0 T.Int

s :: [Var]
s = [i, n]

example :: Graph Loc Edge Inst
example = G.fromLists
  [ (Loc 0, emptyInst (Loc 0) s)
  , (Loc 1, Inst (Loc 1) [] [form|not (i:Int = 13)|])]
  [ ( G.HEdge S.empty (Loc 0), Edge [form|i:Int = 0|] M.empty)
  , ( G.HEdge (S.singleton (Loc 0)) (Loc 0), Edge [form|i/1:Int = i:Int + 2 && i:Int < n:Int|] (M.singleton i i'))
  , ( G.HEdge (S.singleton (Loc 0)) (Loc 1), Edge [form|i:Int >= n:Int|] M.empty)
  ]
