{-# LANGUAGE FlexibleContexts, QuasiQuotes #-}
module Language.Imperative.Concurrent where

import           Language.Imperative
import           Logic.Type as T
import           Logic.Formula
import           Logic.Formula.Parser
import           Logic.Chc
import           Logic.Solver.Z3

import           Control.Monad.State

import           Data.Graph.Inductive.Query.DFS
import           Data.Graph.Inductive.Basic
import           Data.Graph.Inductive.Graph
import           Data.Graph.Inductive.Extras
import qualified Data.Map as M
import           Data.Map (Map)
import qualified Data.Set as S
import           Data.Set (Set)

import           Text.PrettyPrint.HughesPJClass (prettyShow)

data DagState = DagState
  { firstLbl :: Map Node Lbl
  , lastLbl :: Map Node Lbl
  , currentLbl :: Lbl
  } deriving (Show, Eq, Ord)

mkLbl :: State DagState Lbl
mkLbl = do
  l <- currentLbl <$> get
  modify (\s -> s { currentLbl = l + 1 })
  return (l + 1)

newDagState :: DagState
newDagState = DagState M.empty M.empty (-1)

dagTransitions :: FlowGraph -> ([(Lbl, Lbl, Body)], Lbl)
dagTransitions g = evalState (do
  ns <- traverse nodeTransitions (labNodes g)
  es <- traverse edgeTransitions (labEdges g)
  final <- currentLbl <$> get
  return (es ++ concat ns, final)) newDagState
  where
    nodeTransitions (n, bb) = do
      f <- mkLbl
      modify (\s -> s { firstLbl = M.insert n f (firstLbl s) })
      ts <- traverse assign bb
      l <- currentLbl <$> get
      modify (\s -> s { lastLbl = M.insert n l (lastLbl s) })
      return ts

    edgeTransitions (l1, l2, e) = do
      start <- M.findWithDefault undefined l1 <$> (lastLbl <$> get)
      end <- M.findWithDefault undefined l2 <$> (firstLbl <$> get)
      return (start, end, Cond e)

    assign (v, rhs) = do
      start <- currentLbl <$> get
      end <- mkLbl
      return (start, end, Assign v rhs)

data Body = Cond Form | Assign Var RHS
  deriving (Show, Eq, Ord)

data Which = L | R
  deriving (Show, Eq, Ord)

-- | Given a pair of imperative DAGs, construct a CHC system which encodes
-- the conccurrent execution of the two.
conccurentDags :: (Set Var, FlowGraph) -> (Set Var, FlowGraph) -> [Chc]
conccurentDags (vs1, g1) (vs2, g2) =
  let (ts1, ls1) = dagTransitions g1
      (ts2, ls2) = dagTransitions g2 in
  (do (l1, l2, b) <- ts1
      fixed <- [0..ls2]
      return $ rule L vs1 vs2 l1 l2 fixed b) ++
  (do (l1, l2, b) <- ts2
      fixed <- [0..ls1]
      return $ rule R vs1 vs2 l1 l2 fixed b)

rule :: Which -> Set Var -> Set Var -> Lbl -> Lbl -> Lbl -> Body -> Chc
rule w vs1 vs2 l1 l2 fixed b =
  case b of
  Cond f ->
    Rule [App r1 vs] f (App r2 vs)
  Assign v rhs ->
    let v' = v { varName = '$' : varName v }
        hd = App r2 (map (\v'' -> if v == v'' then v' else v'') vs)
        body = case rhs of
          Expr f -> app2 (Eql (typeOf v)) (V v') f
          Arbitrary _ -> LBool True
    in Rule [App r1 vs] body hd
  where
    vs = S.toList $ S.union vs1 vs2
    r1 = Var (curryType (map typeOf vs) T.Bool) n1
    r2 = Var (curryType (map typeOf vs) T.Bool) n2
    n1 = case w of
      L -> "r" ++ show l1 ++ "_" ++ show fixed
      R -> "r" ++ show fixed ++ "_" ++ show l1
    n2 = case w of
      L -> "r" ++ show l2 ++ "_" ++ show fixed
      R -> "r" ++ show fixed ++ "_" ++ show l2

proc1 :: Proc
proc1 =
  [ x := Expr [form|0|]              -- 0
  , Branch [form|x:Int >= n:Int|] 6  -- 1
  , x := Expr [form|x:Int + 1|]      -- 2
  , s := Expr [form|s:Int + 1|]      -- 3
  , s := Expr [form|s:Int + 1|]      -- 4
  , Jump 1                           -- 5
  , Done                             -- 6
  ]
  where
    x = Var T.Int "x"
    s = Var T.Int "s"

proc2 :: Proc
proc2 =
  [ s := Expr [form|s:Int + 1|]
  , Done ]
  where
    s = Var T.Int "s"

reverseReached :: DynGraph gr => Node -> gr n e -> gr n e
reverseReached n g = nfilter (`elem` (reachable n (grev g))) g

testChc =
  let g1 = graph proc1
      g2 = graph proc2
      bs = backEdges g1
      g1' = efilter (`notElem` bs) $ unfold (head $ backEdges g1) g1
      -- g1'' = reverseReached finalLbl g1'
      -- g2' = reverseReached finalLbl g2
      x = Var T.Int "x"
      s = Var T.Int "s"
      n = Var T.Int "n"
      vs1 = S.fromList [x, n, s]
      vs2 = S.fromList [s]
      vars = S.toList $ S.union vs1 vs2

      start = Var (T.Int :=> T.Int :=> T.Int :=> T.Bool) "r0_0"
      end = Var (T.Int :=> T.Int :=> T.Int :=> T.Bool) "r7_1"
  in
  Rule [] [form|s:Int = 0 && n:Int = 2|] (App start vars) :
  conccurentDags (vs1, g1') (vs2, g2)
  ++ [Query [App end vars] (LBool True) [form| s:Int = (2* n:Int) + 1 |]]


disp = mapM_ (print . prettyShow) testChc

fullTest = putStrLn . prettyShow =<< solveChc testChc
