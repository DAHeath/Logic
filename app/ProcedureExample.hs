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
import qualified Logic.Type as T
import           Logic.Formula.Parser
import           Logic.Var

import           Logic.ImplicationGraph.JSONParser (parseGraphFromJSON)
import qualified Data.ByteString.Lazy.Char8 as BS

main :: IO ()
main = do
  G.display "before.dot" example
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

example :: Graph Integer Edge Inst
example = G.fromLists
  [ (0, emptyInst 0 [a])
  , (1, emptyInst 1 [p, x])
  , (2, emptyInst 2 [p, x])
  , (3, Inst 3 [] [form|a:Int = 1|])]

  [ ( G.HEdge S.empty 0, Edge [form|a:Int = 0|] M.empty)
  , ( G.HEdge S.empty 1, Edge [form|x:Int = p:Int|] M.empty)
  , ( G.HEdge (S.singleton 1) 2, Edge [form|x/1:Int = x:Int + 1|] (M.singleton x x'))
  , ( G.HEdge (S.fromList [0, 2]) 3, Edge [form|p:Int = a:Int && a/1:Int = x:Int|] (M.singleton a a'))
  ]
