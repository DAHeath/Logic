{-# LANGUAGE DeriveDataTypeable, LambdaCase #-}
module Language.Imperative where

import           Logic.Type as T
import           Logic.Formula

import           Data.Data (Data)
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Monoid ((<>))
import qualified Data.GraphViz as GV
import qualified Data.Text.Lazy.IO as TIO

import           Data.Graph.Inductive.PatriciaTree
import           Data.Graph.Inductive.Graph

import           Text.PrettyPrint.HughesPJClass ((<+>), Pretty, pPrint)
import qualified Text.PrettyPrint.HughesPJClass as PP

type Lbl = Int

data Command
  = Var := RHS
  | Jump Lbl
  | Branch Form Lbl
  deriving (Show, Eq, Ord, Data)

instance Pretty Command where
  pPrint (v := r) = PP.sep [PP.pPrint v, PP.text ":=", PP.pPrint r]
  pPrint (Jump l) = PP.text "jump" <+> PP.pPrint l
  pPrint (Branch c l) = PP.text "br" <+> PP.pPrint c <+> PP.pPrint l

data RHS
  = Expr Form
  | Arbitrary Type
  deriving (Show, Eq, Ord, Data)

instance Pretty RHS where
  pPrint (Expr f) = PP.pPrint f
  pPrint (Arbitrary t) = PP.text "any_" <> PP.pPrint t

type Proc = [Command]

type BasicBlock = [(Var, RHS)]

data Body = Cond Form | Assign Var RHS
  deriving (Show, Eq, Ord)

instance Pretty Body where
  pPrint = \case
    Cond f -> PP.pPrint f
    Assign v r -> PP.pPrint v <+> PP.text ":=" <+> PP.pPrint r

data FlowGraph = FlowGraph
  { getFlowGraph :: Gr BasicBlock Body
  , initial :: Node
  , terminal :: Node
  } deriving (Show, Eq)

graph :: Proc -> FlowGraph
graph instrs =
  let hs = S.toList $ headers instrs
      cs = separate 0 (tail hs) instrs
      term = length instrs
      ns = zip hs (map block cs) ++ [(term, [])]
      es = concatMap cOut (zip3 hs (tail hs) cs)
      in FlowGraph { getFlowGraph = foldr insEdge (foldr insNode empty ns) es
                   , initial = 0
                   , terminal = term
                   }
  where
    block :: [Command] -> [(Var, RHS)]
    block = \case
      [] -> []
      cs -> concatMap commToAssign $ init cs

    commToAssign :: Command -> [(Var, RHS)]
    commToAssign = \case
      v := rhs -> [(v, rhs)]
      _ -> []
    cOut (here, next, comms') = case comms' of
      [] -> [(here, next, Cond $ LBool True)]
      cs -> case last cs of
        Branch f lbl -> [(here, lbl, Cond f), (here, next, Cond $ Apply Not f)]
        Jump lbl -> [(here, lbl, Cond $ LBool True)]
        v := e -> [(here, next, Assign v e)]

separate :: Lbl -> [Lbl] -> [Command] -> [[Command]]
separate _ [] is = [is]
separate idx (h : hs) is = take (h - idx) is : separate h hs (drop (h - idx) is)

headers :: [Command] -> Set Lbl
headers instrs = S.union (S.fromList [0, length instrs])
                         (S.fromList $ concatMap iHeaders (zip [0..] instrs))
  where
    iHeaders (here, i) = case i of
      _ := _ -> []
      Jump there -> [there]
      Branch _ there -> [here+1, there]

display :: FilePath -> FlowGraph -> IO ()
display fn g =
  let g' = nmap PP.prettyShow $ emap PP.prettyShow (getFlowGraph g)
      params = GV.nonClusteredParams { GV.fmtNode = \ (n,l)  -> [GV.toLabel (show n ++ ": " ++ l)]
                                     , GV.fmtEdge = \ (_, _, l) -> [GV.toLabel l]
                                     }
      dot = GV.graphToDot params g'
  in TIO.writeFile fn (GV.printDotGraph dot)
