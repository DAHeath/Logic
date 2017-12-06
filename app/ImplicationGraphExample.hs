{-# LANGUAGE QuasiQuotes #-}
import Control.Lens
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G
import qualified Data.Optic.Graph.Extras as G
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Maybe (mapMaybe)
import           Data.Text.Prettyprint.Doc

import           Logic.Formula
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Safety
import qualified Logic.Type as T
import           Logic.Formula.Parser
import           Logic.Var
import           Logic.Name

main :: IO ()
main = do
  G.display "before.dot" example
  sol <- solve example
  case sol of
    Left m -> print (pretty m)
    Right r -> do
      G.display "test.dot" r
      print . pretty . M.toList =<< collectAnswer r

i0  = Free (FreeV ["i"] 0 False) T.Int
n0  = Free (FreeV ["i"] 0 False) T.Int
i1  = Free (FreeV ["i"] 1 False) T.Int
n1  = Free (FreeV ["i"] 1 False) T.Int

example :: Graph Loc Form Inst
example = G.fromLists
  [ emp 0 [i0, n0]
  , inst 1 [i1] [form|not (i/1:Int = 3)|]]
  [
    entry 0 ([form|#i/0:Int = 0|])
  , simpleEdge 0 0
      [form|#i/0:Int = i/0:Int + 2 && i/0:Int < n/0:Int
         && #n/0:Int = n/0:Int |]
  , simpleEdge 0 1
    [form|i/0:Int >= n/0:Int && #i/1:Int = i/0:Int|]
  ]

simpleEdge :: Integer -> Integer -> Form -> (G.HEdge Loc, Form)
simpleEdge l1 l2 e = (G.HEdge (S.singleton (Loc l1)) (Loc l2), e)

entry :: Integer -> Form -> (G.HEdge Loc, Form)
entry l e = (G.HEdge S.empty (Loc l), e)

inst :: Integer -> [Var] -> Form -> (Loc, Inst)
inst l vs f = (Loc l, Inst (Loc l) vs f)

emp :: Integer -> [Var] -> (Loc, Inst)
emp l vs = inst l vs (LBool False)
