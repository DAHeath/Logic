{-# LANGUAGE QuasiQuotes #-}
import           Control.Monad.State
import           Control.Monad.Except

import           Data.Optic.Graph (Graph)
import qualified Data.Optic.Graph as G
import qualified Data.Optic.Graph.Extras as G
import qualified Data.Map as M
import           Data.Text.Prettyprint.Doc

import           Logic.ImplicationGraph
import qualified Logic.Type as T
import           Logic.Formula.Parser
import           Logic.Var

main :: IO ()
main = do
  G.display "before" example
  sol <- solve (LinIdx 2 0) example
  case sol of
    Left m -> print (pretty m)
    Right r -> G.display "test" r

stepTest :: IO ()
stepTest = do
  sol <- evalStateT (runExceptT (step (LinIdx 2 0) =<< step (LinIdx 2 0) example)) M.empty
  case sol of
    Left m -> print m
    Right r -> G.display "test" r

i, i', n :: Var
i  = Free "i"  T.Int
i' = Free "i'" T.Int
n  = Free "n"  T.Int

s :: [Var]
s = [i, n]

example :: Graph LinIdx Edge Vert
example = G.fromLists
  [ (LinIdx 0 0, emptyInst [])
  , (LinIdx 1 0, emptyInst s)
  , (LinIdx 2 0, QueryV [form|not (i:Int = 13)|])]
  [ ( LinIdx 0 0, LinIdx 1 0
    , Edge [form|i:Int = 0|] M.empty)
  , ( LinIdx 1 0, LinIdx 1 0
    , Edge [form|i':Int = i:Int + 2 && i:Int < n:Int|] (M.singleton i i'))
  , ( LinIdx 1 0, LinIdx 2 0
    , Edge [form|i:Int >= n:Int|] M.empty)
  ]
