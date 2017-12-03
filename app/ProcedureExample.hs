{-# LANGUAGE QuasiQuotes #-}
import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Except

import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G
import qualified Data.Optic.Graph.Extras as G
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Text.Prettyprint.Doc

import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Safety
import           Logic.ImplicationGraph.LTree
import qualified Logic.Type as T
import           Logic.Formula.Parser
import           Logic.Var

import           Logic.ImplicationGraph.JSONParser (parseGraphFromJSON)
import           Logic.ImplicationGraph.Simplify
import           Logic.ImplicationGraph.StackFragments
import qualified Data.ByteString.Lazy.Char8 as BS

main :: IO ()
main = do
  G.display "before.dot" example
  let toSolve = hyperEdge (Loc 0) (Loc 1) (Loc 1) (G.mapEdge Leaf example)
  G.display "toSolve.dot" toSolve
  sol <- solve example
  case sol of
    Left m -> print (pretty m)
    Right r -> do
      G.display "test.dot" r
      print . pretty . M.toList =<< collectAnswer r

a, a', x, x' :: Var
a  = Free ["a"] 0 T.Int
a' = Free ["a"] 1 T.Int
p  = Free ["p"] 0 T.Int
x  = Free ["x"] 0 T.Int
x' = Free ["x"] 1 T.Int

pr  = Free ["pr"] 0 T.Int
xr  = Free ["xr"] 0 T.Int
pr' = Free ["pr"] 1 T.Int
xr' = Free ["xr"] 1 T.Int

example :: Graph Loc Edge Inst
example = G.fromLists
  [ (Loc 0, emptyInst (Loc 0) [a])
  , (Loc 1, emptyInst (Loc 1) [p, x])
  , (Loc 2, emptyInst (Loc 2) [p, x])
  , (Loc 3, Inst (Loc 3) [] [form|a:Int = 1|])]

  [ ( G.HEdge S.empty (Loc 0), Edge [form|a:Int = 0|] M.empty)
  , ( G.HEdge S.empty (Loc 1), Edge [form|x:Int = p:Int|] M.empty)
  , ( G.HEdge (S.singleton (Loc 1)) (Loc 2), Edge [form|x/1:Int = x:Int + 1|] (M.singleton x x'))
  , ( G.HEdge (S.fromList [Loc 0, Loc 2]) (Loc 3), Edge [form|p:Int = a:Int && a/1:Int = x:Int|] (M.singleton a a'))
  ]

p0, x0 :: Var
p0  = Free ["r0/p"] 0 T.Int
p0' = Free ["r0/p"] 1 T.Int
x0  = Free ["r0/x"] 0 T.Int
x0' = Free ["r0/x"] 1 T.Int

p1, x1 :: Var
p1  = Free ["r1/p"] 0 T.Int
p1' = Free ["r1/p"] 1 T.Int
x1  = Free ["r1/x"] 0 T.Int
x1' = Free ["r1/x"] 1 T.Int

a2 :: Var
a2  = Free ["r2/a"] 0 T.Int

-- f(x) {
--   if (x < 2) {
--     f(x+1)
--   } else {
--     x
--   }
-- }
--

example2 :: Graph Loc Edge Inst
example2 = G.fromLists
  [ (Loc 0, emptyInst (Loc 0) [p0, x0])
  , (Loc 1, emptyInst (Loc 1) [p1, x1])
  , (Loc 2, Inst (Loc 2) [a2] [form|r2/a:Int = 3|])
  ]
  [ ( G.HEdge S.empty (Loc 0), Edge [form|r0/x:Int = r0/p:Int|] M.empty )
  , ( G.HEdge (S.fromList [Loc 0, Loc 1]) (Loc 1),
      Edge [form|r1/p:Int = r0/x:Int + 1
              && r0/p:Int < 3
              && r1/p/1:Int = r0/p:Int
              |] (M.fromList [(p1, p1')]))
  , ( G.HEdge (S.singleton (Loc 0)) (Loc 1),
      Edge [form|r0/p:Int >= 3
              && r1/p:Int = r0/p:Int
              && r1/x:Int = r0/x:Int|] M.empty)
  , ( G.HEdge (S.singleton (Loc 1)) (Loc 2),
      Edge [form|r1/p:Int = 0 && r2/a:Int = r1/x:Int|] M.empty)
  ]
