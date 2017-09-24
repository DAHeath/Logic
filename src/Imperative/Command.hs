{-# LANGUAGE DeriveDataTypeable, LambdaCase, QuasiQuotes #-}
module Imperative.Command where

import           Logic.Type as T
import           Logic.Formula
import           Logic.Formula.Parser

import qualified Data.Map as M
import           Data.Data (Data)
import           Data.List (sort)
import           Data.Bifunctor (second)
import           Data.Monoid ((<>))
import qualified Data.GraphViz as GV
import qualified Data.Text.Lazy.IO as TIO

import           Data.Graph.Inductive.PatriciaTree
import           Data.Graph.Inductive.Graph
import           Data.Graph.Inductive.Basic
import           Data.Graph.Inductive.Query.BFS

import           Text.PrettyPrint.HughesPJClass ((<+>), Pretty, pPrint)
import qualified Text.PrettyPrint.HughesPJClass as PP

type Lbl = Int

data Command
  = Variable := RHS
  | Jump Lbl
  | Branch Form Lbl
  | Done
  deriving (Show, Eq, Ord, Data)

instance Pretty Command where
  pPrint (v := r) = PP.sep [PP.pPrint v, PP.text ":=", PP.pPrint r]
  pPrint (Jump l) = PP.text "jump" <+> PP.pPrint l
  pPrint (Branch c l) = PP.text "br" <+> PP.pPrint c <+> PP.pPrint l
  pPrint Done = PP.text "done"

data RHS
  = Expr Form
  | Arbitrary Type
  deriving (Show, Eq, Ord, Data)

instance Pretty RHS where
  pPrint (Expr f) = PP.pPrint f
  pPrint (Arbitrary t) = PP.text "any_" <> PP.pPrint t

type Proc = [Command]

type BasicBlock = [(Variable, RHS)]

type FlowGraph = Gr BasicBlock Form

graph :: Proc -> FlowGraph
graph instrs =
  let hs = headers instrs
      cs = separate 0 (tail hs) instrs
      ns = zip hs (map (concatMap commToAssign) cs)
      es = concatMap cOut (zip3 hs (tail hs) cs)
  in foldr insEdge (foldr insNode empty ns) es
  where
    commToAssign :: Command -> [(Variable, RHS)]
    commToAssign = \case
      v := rhs -> [(v, rhs)]
      _ -> []
    cOut (here, next, comms') = case comms' of
      [] -> []
      cs -> case last cs of
        Branch f lbl -> [(here, lbl, f), (here, next, Apply Not f)]
        Jump lbl -> [(here, lbl, LBool True)]
        _ -> []

separate :: Lbl -> [Lbl] -> [Command] -> [[Command]]
separate _ [] is = [is]
separate idx (h : hs) is = take (h - idx) is : separate h hs (drop (h - idx) is)

headers :: [Command] -> [Lbl]
headers instrs = sort $ concatMap iHeaders (zip [0..] instrs)
  where
    iHeaders (here, i) = case i of
      _ := _ -> []
      Jump there -> [there]
      Branch _ there -> [here+1, there]
      Done -> []

proc :: Proc
proc =
  [ Branch [form|x:Int >= n:Int|] 5
  , x := Expr [form|x:Int + 1|]
  , s := Expr [form|s:Int + 1|]
  , s := Expr [form|s:Int + 1|]
  , Jump 0
  , Done
  ]
  where
    x = Variable T.Int "x"
    s = Variable T.Int "s"

unfoldEdge :: LEdge e -> Gr n e -> Gr n e
unfoldEdge (l1, l2, b) g =
  let simpl = removeBackedges $ removeReaching l2 g
      rev = grev simpl
      allPs = bft l1 rev
      ps = concat $ filter (\case
                             [] -> False
                             ls -> head ls == l2 && last ls == l1) allPs
      g' = subgraph ps simpl
      ns = nodes g'
      m = M.fromList (zip ns (newNodes (length ns) g))
      rel n = M.findWithDefault undefined n m
      relabelled = gmap (\(adjl, l, n, adjr) -> ( map (second rel) adjl
                                                , rel l
                                                , n
                                                , map (second rel) adjr)) g'
      toReroute = filter (\(l1, l2, _) -> l1 `notElem` ns && l2 `elem` ns) (labEdges g)
      reroutesRemoved = efilter (`notElem` toReroute) g
      merged = foldr insEdge (foldr insNode reroutesRemoved
                                            (labNodes relabelled))
                             (labEdges relabelled)
      connected = insEdge (rel l1, l2, b) merged
      rerouted = foldr (\(l1, l2, b) gr -> insEdge (l1, rel l2, b) gr) connected toReroute
  in rerouted

display :: FilePath -> FlowGraph -> IO ()
display fn g =
  let g' = nmap PP.prettyShow $ emap PP.prettyShow g
      params = GV.nonClusteredParams { GV.fmtNode = \ (_,l)  -> [GV.toLabel l]
                                     , GV.fmtEdge = \ (_, _, l) -> [GV.toLabel l]
                                     }
      dot = GV.graphToDot params g'
  in TIO.writeFile fn (GV.printDotGraph dot)

removeBackedges :: FlowGraph -> FlowGraph
removeBackedges = efilter (\(l1, l2, _) -> l1 < l2)

backEdges :: Gr n e -> [LEdge e]
backEdges = filter (\(l1, l2, _) -> l2 < l1) . labEdges

removeReaching :: Lbl -> FlowGraph -> FlowGraph
removeReaching l = efilter (\(_, l2, _) -> l2 /= l)
