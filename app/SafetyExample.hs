{-# LANGUAGE QuasiQuotes #-}
module SafetyExample where

import           Data.Functor.Identity
import qualified Data.Map as M
import           Data.Text.Prettyprint.Doc
import           Data.Loc
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Graph.Extras as G

import           Logic.ImplicationGraph
import           Logic.Formula as F
import           Logic.Solver.Safety

import           Language.Structured

example :: IO ()
example = do
  G.display "before.dot" g
  sol <- solve [form|not (i = 7)|] g
  case sol of
    Left m -> print (pretty m)
    Right r -> do
      G.display "test.dot" r
      print . pretty . M.toList =<< collectAnswer r

i, n :: Var
i  = Var ["i"] 0 False F.Int
n  = Var ["n"] 0 False F.Int

g :: Graph Loc (Identity Form) Inst
g = singleNonRec
  [ (i := [form|0|], [i,n])
  , ( While [form|i < n|]
        [ (i := [form|i + 2|], [i,n]) ]
    , [i, n])
  ]
