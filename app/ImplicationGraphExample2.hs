{-# LANGUAGE QuasiQuotes #-}

import qualified Data.Map as M
import qualified Data.Ord.Graph as G
import qualified Data.Ord.Graph.Extras as G

import           Logic.ImplicationGraph.Type2

import qualified Logic.Type as T
import           Logic.Formula.Parser
import           Logic.Var

import           Text.PrettyPrint.HughesPJClass

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
  query (LinIdx 2 0) [form|not (i:Int = 41)|]
  emptyImplGr
