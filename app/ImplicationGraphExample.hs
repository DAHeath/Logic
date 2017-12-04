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

i0  = Free (NoAlias (Located 0 ["i"])) T.Int
n0  = Free (NoAlias (Located 0 ["n"])) T.Int
i1  = Free (NoAlias (Located 1 ["i"])) T.Int
n1  = Free (NoAlias (Located 1 ["n"])) T.Int

example :: Graph Loc (Form BasicName) (Inst BasicName)
example = G.fromLists
  [ emp 0 [i0, n0]
  , inst 1 [i1] [form|not (v1/i:Int = 7)|]]
  [
    entry 0 ([form|#v0/i:Int = 0|])
  , simpleEdge 0 0
      [form|#v0/i:Int = v0/i:Int + 2 && v0/i:Int < v0/n:Int
         && #v0/n:Int = v0/n:Int |]
  , simpleEdge 0 1
    [form|v0/i:Int >= v0/n:Int && #v1/i:Int = v0/i:Int|]
  ]

simpleEdge :: Integer -> Integer -> Form BasicName -> (G.HEdge Loc, Form BasicName)
simpleEdge l1 l2 e = (G.HEdge (S.singleton (Loc l1)) (Loc l2), e)

entry :: Integer -> Form BasicName -> (G.HEdge Loc, Form BasicName)
entry l e = (G.HEdge S.empty (Loc l), e)

inst :: Integer -> [Var BasicName] -> Form BasicName -> (Loc, Inst BasicName)
inst l vs f = (Loc l, Inst (Loc l) vs f)

emp :: Integer -> [Var BasicName] -> (Loc, Inst BasicName)
emp l vs = inst l vs (LBool False)
