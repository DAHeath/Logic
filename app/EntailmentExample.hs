{-# LANGUAGE QuasiQuotes #-}

import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Graph.Inductive.Extras as G
import qualified Data.Map as M

import           Logic.Entailment
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

g' :: Entailment
g' = foldBackedges [3] g

main :: IO ()
main = do
  sol <- solve g'
  case sol of
    Left m -> putStrLn $ prettyShow m
    Right g'' -> G.display "test" g''
