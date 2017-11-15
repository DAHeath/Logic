{-# LANGUAGE QuasiQuotes #-}
import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Except

import           Data.Optic.Graph (Graph)
import qualified Data.Optic.Graph as G
import qualified Data.Optic.Graph.Extras as G
import qualified Data.Map as M
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
  sol <- solve example hs
  case sol of
    Left m -> print (pretty m)
    Right r -> do
      G.display "test.dot" (r ^. implGr)
      print . pretty . M.toList =<< collectAnswer r

a, a', x, x' :: Var
a  = Free ["a"] 0 T.Int
a' = Free ["a"] 1 T.Int
p  = Free ["p"] 0 T.Int
x  = Free ["x"] 0 T.Int
x' = Free ["x"] 1 T.Int

example :: Graph Integer Edge Vert
example = G.fromLists
  [ (0, emptyInst [])
  , (1, emptyInst [a])

  , (2, emptyInst [p, x])

  , (3, emptyInst [p, x])
  , (4, QueryV [form|a:Int = 1|])]

  [ ( 0, 1, Edge [form|a:Int = 0|] M.empty)
  , ( 0, 2, Edge [form|x:Int = p:Int|] M.empty)
  , ( 2, 3, Edge [form|x/1:Int = x:Int + 1|] (M.singleton x x'))
  , ( 1, 4, Edge [form|true|] M.empty)
  , ( 3, 4, Edge [form|p:Int = a:Int && a/1:Int = x:Int|] (M.singleton a a'))
  ]

hs :: HyperEdges
hs = M.singleton 4 [(1, 3)]
