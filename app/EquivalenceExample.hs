{-# LANGUAGE QuasiQuotes #-}
module EquivalenceExample where

import           Data.Functor.Identity
import           Data.Text.Prettyprint.Doc
import           Data.Loc
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Graph.Extras as G

import           Logic.Formula as F
import           Logic.ImplicationGraph
import           Logic.Solver.Equivalence

import           Language.Structured

r, n, m, x :: Var
r = Var ["r"] 0 False F.Int
n = Var ["n"] 0 False F.Int
m = Var ["m"] 0 False F.Int
x = Var ["x"] 0 False F.Int

ad0 :: Graph Loc (Identity Form) Inst
ad0 = singleNonRec
  [ (r := [form|n - 9 * ((n - 1) / 9)|], [r, n]) ]

ad1 :: Graph Loc (Identity Form) Inst
ad1 = singleNonRec
  [ (x := [form|m|], [x, m])
  , (While [form|x > 9|]
      [ (x := [form|x / 10 + x % 10|], [x, m]) ], [x, m])
  ]

example :: IO ()
example = do
  sol <- solve
    [form|n > 0 && n = m -> x = r|] ad0 ad1
  case sol of
    Left e -> print (pretty e)
    Right sol' ->
      G.display "sol" sol'
