import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Extras

graph1, graph2 :: Gr Int ()
graph1 =
  foldr insEdge
    (foldr insNode empty [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4)])
    [(0, 1, ()), (1, 2, ()), (1, 3, ()), (2, 4, ()), (3, 4, ())]
graph2 =
  foldr insEdge
    (foldr insNode empty [(0, 0), (1, 1), (2, 2), (3, 3)])
    [(0, 1, ()), (1, 2, ()), (1, 3, ())]
graph3 :: Gr (Int, Int) ()
graph3 = cartesianProduct (,) graph1 graph2

main :: IO ()
main = do
  display "graph1" graph1
  display "graph2" graph2
  display "graph3" graph3
