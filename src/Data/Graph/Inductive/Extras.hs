{-# LANGUAGE TypeFamilies, OverloadedStrings #-}
module Data.Graph.Inductive.Extras where

import           Control.Lens hiding (pre)

import qualified Data.Tree as T
import           Data.Tree (Tree)
import           Data.Maybe (fromJust)
import           Data.Graph.Inductive.PatriciaTree
import           Data.Graph.Inductive.Graph
import           Data.Graph.Inductive.Basic
import           Data.Graph.Inductive.Query.DFS
import           Data.Graph.Inductive.Query.BFS
import           Data.Monoid ((<>))

import qualified Data.GraphViz as GV
import qualified Turtle
import qualified Data.Text.Lazy.IO as TIO

import           Text.PrettyPrint.HughesPJClass (Pretty, prettyShow)

rebuildFrom :: Int -> Gr n e -> Gr n e
rebuildFrom bot g =
  let ns = labNodes g
      es = labEdges g
      ns' = map (\(n, l) -> (n+bot, l)) ns
      es' = map (\(n1, n2, e) -> (n1+bot, n2+bot, e)) es
  in foldr insEdge (foldr insNode empty ns') es'

-- | Combine two graphs
overlay :: Gr n e -> Gr n e -> Gr n e
overlay g g' = foldr insEdge (foldr insNode g (labNodes g')) (labEdges g')

subgraphBetween :: Node -> Node -> Gr n e -> Gr n e
subgraphBetween l1 l2 g =
  let simpl = removeBackedges $ removeReaching l2 g
      rev = grev simpl
      allPs = bft l1 rev
      ps = concat $ filter (\case
                             [] -> False
                             ls -> head ls == l2 && last ls == l1) allPs
  in subgraph ps simpl

removeBackedges :: Gr n e -> Gr n e
removeBackedges = efilter (\(l1, l2, _) -> l1 <= l2)

backEdges :: Gr n e -> [LEdge e]
backEdges = filter (\(l1, l2, _) -> l2 <= l1) . labEdges

removeReaching :: DynGraph gr => Node -> gr n e -> gr n e
removeReaching l = efilter (\(_, l2, _) -> l2 /= l)

reverseReached :: DynGraph gr => Node -> gr n e -> gr n e
reverseReached n g = nfilter (`elem` reachable n (grev g)) g

ancestors :: DynGraph gr => gr n e -> Node -> [Node]
ancestors g n = filter (/= n) $ nodes $ reverseReached n g

cartesianProduct :: (Graph gr, DynGraph gr')
                 => (a -> b -> c) -> gr a e -> gr b e -> gr' c e
cartesianProduct f g1 g2 =
  if order g2 == 0 then empty else
    let ns1 = labNodes g1
        ns2 = labNodes g2
        high = maximum (map fst ns2)+1
        ns = do
          (n1, l1) <- ns1
          (n2, l2) <- ns2
          return (n1*high + n2, f l1 l2)
        ls1 = labEdges g1
        ls2 = labEdges g2
        ls1' = do
          (n2, _) <- ns2
          (n1, n1', l) <- ls1
          return (n1*high + n2, n1'*high + n2, l)
        ls2' = do
          (n1, _) <- ns1
          (n2, n2', l) <- ls2
          return (n1*high + n2, n1*high + n2', l)
    in foldr insEdge (foldr insNode empty ns) (ls1' ++ ls2')

-- | Unfold the graph with respect to a given backedge.
-- unfold :: (LEdge ImplGrEdge) -> ImplGr -> ImplGr
unfold :: Eq b => LEdge b -> Gr a b -> Gr a b
unfold (l1, l2, b) g =
  let g' = subgraphBetween l1 l2 g
      ns = nodes g'
      -- remove the edges which enter the expanded subgraph
      incoming = filter (\(l1', l2', _) -> l1' `notElem` ns && l2' `elem` ns) (labEdges g)
      outgoing = filter (\(l1', l2', _) -> l1' `elem` ns && l2' `notElem` ns) (labEdges g)
      incomingRemoved = efilter (`notElem` incoming) g
      -- relabel the subgraph
      diff = order g - 1
      relabelled = rebuildFrom diff g'

      -- set the facts on the unfolded nodes to true
      merged = overlay incomingRemoved relabelled
      connected = insEdge (l1 + diff, l2, b) merged
      incRerouted = foldr (\(l1', l2', b') gr -> insEdge (l1', l2' + diff, b') gr)
                          connected incoming
      outDuplicated = foldr (\(l1', l2', b') gr -> insEdge (l1' + diff, l2', b') gr)
                            incRerouted outgoing

  in outDuplicated


treeFrom :: Graph gr => Node -> gr a b -> Tree (Node, a)
treeFrom idx dag =
  T.Node (idx, vertex idx dag) (map (`treeFrom` dag) (suc dag idx))

vertex :: Graph gr => Node -> gr a b -> a
vertex n g = fromJust (lab g n)

display :: (Pretty n, Pretty e) => FilePath -> Gr n e -> IO ()
display fn g =
  let g' = nmap prettyShow $ emap prettyShow g
      params = GV.nonClusteredParams { GV.fmtNode = \ (n,l)  -> [GV.toLabel (show n ++ ": " ++ l)]
                                     , GV.fmtEdge = \ (_, _, l) -> [GV.toLabel l]
                                     }
      dot = GV.graphToDot params g'
  in do
    TIO.writeFile fn (GV.printDotGraph dot)
    let fn' = Turtle.fromString fn
    _ <- Turtle.shell ("dot -Tpdf " <> fn' <> "> " <> fn' <> ".pdf") Turtle.empty
    _ <-Turtle.shell ("open " <> fn' <> ".pdf") Turtle.empty
    return ()

type instance Index (Gr n e) = Node
type instance IxValue (Gr n e) = n
instance Ixed (Gr n e) where
instance At (Gr n e) where
  at n f g = f mv <&> \r -> case r of
    Nothing -> maybe g (const (delNode n g)) mv
    Just v' -> gmap (\(bef, n', v, aft) -> if n == n' then (bef, n', v', aft)
                                                      else (bef, n', v, aft)) g
    where mv = lab g n
