{-# LANGUAGE QuasiQuotes #-}
import           Control.Monad.State
import           Control.Monad.Except

import           Data.Ord.Graph (Graph)
import qualified Data.Ord.Graph as G
import qualified Data.Ord.Graph.Extras as G
import qualified Data.Map as M

import           Logic.ImplicationGraph.Solve
import           Logic.ImplicationGraph.Type
import qualified Logic.Type as T
import           Logic.Formula.Parser
import           Logic.Var

import           Text.PrettyPrint.HughesPJClass

main :: IO ()
main = do
  G.display "before" g
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
  G.fromLists
    [ ((0, 0), InstanceNode $ emptyInstance [])
    , ((1, 0), InstanceNode $ emptyInstance s)
    , ((2, 0), QueryNode [form|not (i:Int = 41)|])
    ]
    [ ((0, 0), (1, 0), ImplGrEdge [form|i:Int = 0|] M.empty)
    , ((1, 0), (1, 0), ImplGrEdge [form|i':Int = i:Int + 2 && i:Int < n:Int|]
                                      (M.singleton i i'))
    , ((1, 0), (2, 0), ImplGrEdge [form|i:Int >= n:Int|] M.empty)
    ]

bs = G.backEdges g
-- g' = foldBackedges bs g
