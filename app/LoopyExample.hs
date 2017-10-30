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
  sol <- solve (LinIdx 3 0) example
  case sol of
    Left m -> print (pretty m)
    Right r -> do
      G.display "after" r
      print $ pretty $ M.toList $ collectAnswer r

stepTest :: IO ()
stepTest = do
  sol <- evalStateT (runExceptT (step (LinIdx 2 0) =<< step (LinIdx 2 0) example)) M.empty
  case sol of
    Left m -> print m
    Right r -> G.display "test" r

i, i', j, j', c, c' :: Var
i  = Free "i"  T.Int
i' = Free "i'" T.Int
j  = Free "j"  T.Int
j' = Free "j'" T.Int
c  = Free "c"  T.Int
c' = Free "c'" T.Int

example :: Graph LinIdx Edge Vert
example = G.fromLists
  [ (LinIdx 0 0, emptyInst [])
  , (LinIdx 1 0, emptyInst [i, c])
  , (LinIdx 2 0, emptyInst [i, j, c])
  , (LinIdx 3 0, QueryV [form|c:Int = 9|])
  ]

  [ (LinIdx 0 0, LinIdx 1 0, Edge [form|i:Int = 0 && c:Int = 0|] M.empty)
  , (LinIdx 1 0, LinIdx 2 0,
    Edge [form|i:Int < 3
            && j:Int = 0
            && i':Int = i:Int+1|] (M.fromList [(i, i')]))
  , (LinIdx 1 0, LinIdx 3 0, Edge [form|i:Int >= 3|] M.empty)
  , (LinIdx 2 0, LinIdx 2 0,
    Edge [form|j:Int < 3
            && c':Int = c:Int+1
            && j':Int = j:Int+1 |] (M.fromList [(c, c'), (j, j')]))
  , (LinIdx 2 0, LinIdx 1 0, Edge [form|j:Int >= 3|] M.empty)
  ]

steppy :: IO ()
steppy = void $ runSolve (loop example)
  where
    loop g = do
      g' <- step (LinIdx 3 0) g
      G.display "step" g'
      _ <- liftIO getLine
      loop g'
