{-# LANGUAGE QuasiQuotes #-}
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G
import qualified Data.Optic.Graph.Extras as G
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Text.Prettyprint.Doc

import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Safety
import           Logic.ImplicationGraph.Shape
import qualified Logic.Type as T
import           Logic.Formula.Parser
import           Logic.Var

import           Language.Structured

i, n, h, c, o, v, l:: Var
i = Var ["i"] 0 False T.Int
n = Var ["n"] 0 False T.Int
h = Var ["h"] 0 False T.Int
c = Var ["c"] 0 False T.Int
o = Var ["o"] 0 False T.Int
v = Var ["v"] 0 False T.Int
l = Var ["l"] 0 False T.Int

example :: Graph Loc Edge Inst
example = singleNonRec
  [ (i := [form|1|]                     , [i,n])
  , (h := [form|0|]                     , [i,n,h])
  , (c := [form|0|]                     , [i,n,h,c])
  , ( While [form|c < n|]
        [ (Store o v [form|i|] [form|h|], [i,n,h,c,o,v])
        , (h := [form|i|]               , [i,n,h,c,o,v])
        , (i := [form|i+1|]             , [i,n,h,c,o,v])
        , (c := [form|c+1|]             , [i,n,h,c,o,v])
        ]                               , [i,n,h,c,o,v])
  , (c := [form|0|]                     , [n,h,c])
  , ( While [form|c < n|]
        [ (Load l h [form|h|]           , [n,h,c,l])
        , (c := [form|c+1|]             , [n,h,c,l])
        ]                               , [n,h,c,l])
  ]

main :: IO ()
main = do
  G.display "shape" example
  let g = shapeAugment (S.fromList [o]) (S.fromList [l]) $
        unwindAll mempty $
        unwindAll mempty $
        unwindAll mempty $
        fromGraph example
  G.display "unwound1" g
  print g
  -- sol <- solve [form|h = 0|] example

--   case sol of
--     Left e -> print (pretty e)
--     Right sol' ->
--       G.display "sol" sol'
