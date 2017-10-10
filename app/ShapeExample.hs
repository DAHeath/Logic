{-# LANGUAGE QuasiQuotes #-}

import           Control.Monad.State

import           Data.Graph.Inductive.PatriciaTree
import           Data.Graph.Inductive.Basic
import           Data.Graph.Inductive.Graph
import           Data.Graph.Inductive.Extras
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S

import qualified Logic.Type as T
import           Logic.Formula
import           Logic.Formula.Parser
import           Logic.Var
import           Language.Imperative
-- import           Language.Imperative.Shape

h, t, i, c, n :: Var
h = Free "h" T.Int
t = Free "t" T.Int
i = Free "i" T.Int
c = Free "c" T.Int
n = Free "n" T.Int

example :: Comm
example = Seq
  (Ass h (Expr [form|1|])) $ Seq
  (Ass t (Expr (V h))) $ Seq
  (Ass i (Expr [form|2|])) $ Seq
  (Ass c (Expr [form|0|])) $ Seq
  (Loop [form|c:Int < n:Int|] $ Seq
    (Store "next" (V t) (V i)) $ Seq
    (Ass t (Expr (V i)))
    (Ass i (Expr [form|i:Int + 1|]))) $ Seq
  (Ass c (Expr [form|0|]))
  (Loop [form|c:Int < n:Int|]
    (Ass h (Select "next" (V h))))


g, g' :: Gr () SemAct
g = commGraph example
g' = efilter (`notElem` b) $ unfold (b !! 1) (unfold (head b) g)

b :: [LEdge SemAct]
b = backEdges g

hasStore :: SemAct -> Bool
hasStore SemStore{} = True
hasStore (SemSeq s1 s2) = hasStore s1 || hasStore s2
hasStore _ = False

storePositions :: Gr a SemAct -> Set Node
storePositions = ufold (\ctx ns -> S.union (ctxStores ctx) ns) S.empty
  where
    ctxStores :: Context a SemAct -> Set Node
    ctxStores (bef, n, _, aft) =
      let nStore = if any (hasStore.fst) aft then S.singleton n else S.empty
          inStore = S.unions $
             map (\(ac, n') -> if hasStore ac then S.singleton n' else S.empty) bef
      in S.union nStore inStore

main :: IO ()
main = do
  display "shape" g
  display "shape-u1" g'
