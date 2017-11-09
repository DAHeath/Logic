{-# LANGUAGE QuasiQuotes #-}
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
  sol <- solve 2 example
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

example :: Graph Integer Edge Vert
example = G.fromLists
  [ (0, emptyInst [])
  , (1, emptyInst s)
  , (2, QueryV [form|not (i:Int = 11)|])]
  [ ( 0, 1, Edge [form|i:Int = 0|] M.empty)
  , ( 1, 1, Edge [form|i/1:Int = i:Int + 2 && i:Int < n:Int|] (M.singleton i i'))
  , ( 1, 2, Edge [form|i:Int >= n:Int|] M.empty)
  ]
