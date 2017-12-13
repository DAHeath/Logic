{-# LANGUAGE QuasiQuotes #-}
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Graph.Extras as G
import qualified Data.Map as M
import           Data.Text.Prettyprint.Doc

import           Logic.ImplicationGraph
import           Logic.Formula as F
import           Logic.Solver.Safety

import           Language.Structured

main :: IO ()
main = do
  G.display "before.dot" example
  sol <- solve [form|not (i = 7)|] example
  case sol of
    Left m -> print (pretty m)
    Right r -> do
      G.display "test.dot" r
      print . pretty . M.toList =<< collectAnswer r

i, n :: Var
i  = Var ["i"] 0 False F.Int
n  = Var ["n"] 0 False F.Int

example :: Graph Loc Edge Inst
example = singleNonRec
  [ (i := [form|0|], [i,n])
  , ( While [form|i < n|]
        [ (i := [form|i + 2|], [i,n]) ]
    , [i, n])
  ]
