{-# LANGUAGE QuasiQuotes #-}
import           Control.Monad.State
import           Control.Monad.Except

import           Data.Ord.Graph (Graph)
import qualified Data.Ord.Graph as G
import qualified Data.Ord.Graph.Extras as G
import qualified Data.Map as M

import           Logic.ImplicationGraph
import qualified Logic.Type as T
import           Logic.Formula.Parser
import           Logic.Var

import           Text.PrettyPrint.HughesPJClass

main :: IO ()
main = do
  G.display "before" example
  sol <- solve (LinIdx 2 0) example
  case sol of
    Left m -> putStrLn (prettyShow m)
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

example =
  edge (LinIdx 0 0) (LinIdx 1 0) [form|i:Int = 0|] M.empty $
  edge (LinIdx 1 0) (LinIdx 1 0) [form|i':Int = i:Int + 2 && i:Int < n:Int|] (M.singleton i i') $
  edge (LinIdx 1 0) (LinIdx 2 0) [form|i:Int >= n:Int|] M.empty $
  emptyInst (LinIdx 0 0) [] $
  emptyInst (LinIdx 1 0) s $
  query (LinIdx 2 0) [form|not (i:Int = 13)|]
  emptyImplGr
