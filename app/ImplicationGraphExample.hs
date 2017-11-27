{-# LANGUAGE QuasiQuotes #-}
import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Except

import           Data.Optic.Directed.Graph (Graph)
import qualified Data.Optic.Directed.Graph as G
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
  sol <- solve example M.empty
  case sol of
    Left m -> print (pretty m)
    Right r -> do
      G.display "test.dot" (r ^. implGr)
      -- print . pretty . M.toList =<< collectAnswer r

i, i', n :: Var
i  = Free ["i"] 0 T.Int
i' = Free ["i"] 1 T.Int
n  = Free ["n"] 0 T.Int

s :: [Var]
s = [i, n]

example :: Graph Integer Edge Vert
example = G.fromLists
  [ (0, emptyInst 0 [])
  , (1, emptyInst 1 s)
  , (2, QueryV [form|not (i:Int = 3)|])]
  [ ( G.Pair 0 1, Edge [form|i:Int = 0|] M.empty)
  , ( G.Pair 1 1, Edge [form|i/1:Int = i:Int + 2 && i:Int < n:Int|] (M.singleton i i'))
  , ( G.Pair 1 2, Edge [form|i:Int >= n:Int|] M.empty)
  ]
