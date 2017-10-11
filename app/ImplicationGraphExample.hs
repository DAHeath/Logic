{-# LANGUAGE QuasiQuotes #-}
import           Control.Monad.State
import           Control.Monad.Except

import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Graph.Inductive.Extras as G
import qualified Data.Map as M

import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Type
import qualified Logic.Type as T
import           Logic.Formula.Parser
import           Logic.Var

import           Text.PrettyPrint.HughesPJClass

main :: IO ()
main = do
  sol <- solve [3] g
  case sol of
    Left m -> putStrLn (prettyShow m)
    Right r -> G.display "test" r

i, i', n :: Var
i  = Free "i"  T.Int
i' = Free "i'" T.Int
n  = Free "n"  T.Int

s :: [Var]
s = [i, n]

g :: ImplGr
g =
  G.insEdge (0, 1, ImplGrEdge [form|i:Int = 0|] M.empty) $
  G.insEdge (1, 1, ImplGrEdge [form|i':Int = i:Int + 2 && i:Int < n:Int|]
                                  (M.singleton i i')) $
  G.insEdge (1, 2, ImplGrEdge [form|i:Int >= n:Int|] M.empty) $
  G.insEdge (2, 3, ImplGrEdge [form|true|] M.empty) $
  G.insNode (0, InstanceNode (mkInstance [0] [])) $
  G.insNode (1, InstanceNode (mkInstance [1] s)) $
  G.insNode (2, InstanceNode (mkInstance [2] s)) $
  G.insNode (3, QueryNode [form|not (i:Int = 3)|])
  G.empty

bs = backEdges [3] g
g' = foldBackedges bs g
