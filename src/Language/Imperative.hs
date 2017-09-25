{-# LANGUAGE DeriveDataTypeable, LambdaCase #-}
module Language.Imperative where

import           Logic.Type as T
import           Logic.Formula

import           Data.Data (Data)
import           Data.List (sort)
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Monoid ((<>))
import qualified Data.GraphViz as GV
import qualified Data.Text.Lazy.IO as TIO

import           Data.Graph.Inductive.PatriciaTree
import           Data.Graph.Inductive.Graph

import           Text.PrettyPrint.HughesPJClass ((<+>), Pretty, pPrint)
import qualified Text.PrettyPrint.HughesPJClass as PP

import Data.Graph.Inductive.Extras

type Lbl = Int

data Command
  = Var := RHS
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

type BasicBlock = [(Var, RHS)]

type FlowGraph = Gr BasicBlock Form

initLbl :: Lbl
initLbl = -1

finalLbl :: Lbl
finalLbl = maxBound

graph :: Proc -> FlowGraph
graph instrs =
  let hs = S.toList $ headers instrs
      cs = separate 0 (tail hs) instrs
      ns = zip hs (map (concatMap commToAssign) cs)
      es = concatMap cOut (zip3 (-1 : hs) (hs ++ [finalLbl]) ([] : cs))
      in foldr insEdge (foldr insNode
               (insNode (finalLbl, []) $ insNode (initLbl, []) empty)
               ns) es
  where
    commToAssign :: Command -> [(Var, RHS)]
    commToAssign = \case
      v := rhs -> [(v, rhs)]
      _ -> []
    cOut (here, next, comms') = case comms' of
      [] -> [(here, next, LBool True)]
      cs -> case last cs of
        Branch f lbl -> [(here, lbl, f), (here, next, Apply Not f)]
        Jump lbl -> [(here, lbl, LBool True)]
        Done -> [(here, finalLbl, LBool True)]
        _ := _ -> [(here, next, LBool True)]

separate :: Lbl -> [Lbl] -> [Command] -> [[Command]]
separate _ [] is = [is]
separate idx (h : hs) is = take (h - idx) is : separate h hs (drop (h - idx) is)

headers :: [Command] -> Set Lbl
headers instrs = S.insert 0 (S.fromList $ concatMap iHeaders (zip [0..] instrs))
  where
    iHeaders (here, i) = case i of
      _ := _ -> []
      Jump there -> [there]
      Branch _ there -> [here+1, there]
      Done -> []

display :: FilePath -> FlowGraph -> IO ()
display fn g =
  let g' = nmap PP.prettyShow $ emap PP.prettyShow g
      params = GV.nonClusteredParams { GV.fmtNode = \ (_,l)  -> [GV.toLabel l]
                                     , GV.fmtEdge = \ (_, _, l) -> [GV.toLabel l]
                                     }
      dot = GV.graphToDot params g'
  in TIO.writeFile fn (GV.printDotGraph dot)
