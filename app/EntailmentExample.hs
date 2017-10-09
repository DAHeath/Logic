{-# LANGUAGE QuasiQuotes #-}

import qualified Data.Graph.Inductive.Basic as G
import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Graph.Inductive.PatriciaTree as G
import qualified Data.Graph.Inductive.Extras as G
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Tree (Tree)
import qualified Data.Tree as T

import           Logic.Entailment
import qualified Logic.Type as T
import           Logic.Formula
import           Logic.Formula.Parser
import           Logic.Var
import           Logic.Solver.Z3

import           Text.PrettyPrint.HughesPJClass

i, i', n :: Var
i  = Free "i"  T.Int
i' = Free "i'" T.Int
n  = Free "n"  T.Int

s :: [Var]
s = [i, n]

g :: Entailment
g =
  G.insEdge (0, 1, EntailmentEdge [form|i:Int = 0|] M.empty) $
  G.insEdge (1, 1, EntailmentEdge [form|i':Int = i:Int + 2 && i:Int < n:Int|]
                                  (M.singleton i i')) $
  G.insEdge (1, 2, EntailmentEdge [form|i:Int >= n:Int|] M.empty) $
  G.insNode (0, InstanceNode (mkInstance [0] s)) $
  G.insNode (1, InstanceNode (mkInstance [1] s)) $
  G.insNode (2, QueryNode [form|not (i:Int = 41)|])
  G.empty

b :: [G.LEdge EntailmentEdge]
b = backEdges [3] g

g' :: Entailment
g' = G.efilter (`notElem` b) g

main :: IO ()
main = do
  sol <- solve g'
  case sol of
    Left m -> putStrLn $ prettyShow m
    Right g'' -> G.display "test" g''
