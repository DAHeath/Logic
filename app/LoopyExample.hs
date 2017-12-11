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

main :: IO ()
main = do
  G.display "before" example
  sol <- solve example
  case sol of
    Left m -> print (pretty m)
    Right r -> G.display "after" r

i, i', j, j', c, c' :: Var
i  = Free ["i"] 0 T.Int
i' = Free ["i"] 1 T.Int
j  = Free ["j"] 0 T.Int
j' = Free ["j"] 1 T.Int
c  = Free ["c"] 0 T.Int
c' = Free ["c"] 1 T.Int

example :: Graph Integer Edge Inst
example = G.fromLists
  [ (0, emptyInst 0 [i, c])
  , (1, emptyInst 1 [i, j, c])
  , (2, Inst 2 [] [form|c = 1|])
  ]

  [ (G.HEdge S.empty 0, Edge [form|i = 0 && c = 0|] M.empty)
  , (G.HEdge (S.singleton 0) 1,
    Edge [form|i < 1
            && j = 0
            && i/1 = i+1|] (M.fromList [(i, i')]))
  , (G.HEdge (S.singleton 0) 2, Edge [form|i >= 1|] M.empty)
  , (G.HEdge (S.singleton 1) 1,
    Edge [form|j < 1
            && c/1 = c+1
            && j/1 = j+1 |] (M.fromList [(c, c'), (j, j')]))
  , (G.HEdge (S.singleton 1) 0, Edge [form|j >= 1|] M.empty)
  ]

-- steppy :: IO ()
-- steppy = void $ runSolve (loop example)
--   where
--     loop g = do
--       g' <- step 3 g
--       G.display "step" g'
--       _ <- liftIO getLine
--       loop g'
