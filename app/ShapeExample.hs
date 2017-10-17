{-# LANGUAGE QuasiQuotes, LambdaCase #-}

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Except

import qualified Data.Ord.Graph.Extras as G
import qualified Data.Ord.Graph as G
import qualified Data.Map as M
import           Data.Maybe

import qualified Logic.Type as T
import           Logic.Formula
import           Logic.Formula.Parser
import           Logic.Var
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Type
import           Text.PrettyPrint.HughesPJClass

import Debug.Trace

h, h', t, t', i, i', c, c', n, next, next' :: Var
h  = Free "h"  T.Int
h' = Free "h'" T.Int
t  = Free "t"  T.Int
t' = Free "t'" T.Int
i  = Free "i"  T.Int
i' = Free "i'" T.Int
c  = Free "c"  T.Int
c' = Free "c'" T.Int
n  = Free "n" T.Int
next  = Free "next" (T.Array T.Int T.Int)
next' = Free "next" (T.Array T.Int T.Int)

s :: [Var]
s = [h, t, i, c, n, next]

-- example :: Comm
-- example = Seq
--   (Ass h (Expr [form|1|])) $ Seq
--   (Ass t (Expr (V h))) $ Seq
--   (Ass i (Expr [form|2|])) $ Seq
--   (Ass c (Expr [form|0|])) $ Seq
--   (Loop [form|c:Int < n:Int|] $ Seq
--     (Save "next" (V t) (V i)) $ Seq
--     (Ass t (Expr (V i)))
--     (Ass i (Expr [form|i:Int + 1|]))) $ Seq
--   (Ass c (Expr [form|0|]))
--   (Loop [form|c:Int < n:Int|]
--     (Ass h (Load "next" (V h))))

g :: ImplGr
g =

  G.fromLists
    [ (([0], 0), InstanceNode $ emptyInstance [])
    , (([1], 0), InstanceNode $ emptyInstance s)
    , (([2], 0), InstanceNode $ emptyInstance s)
    , (([3], 0), QueryNode [form|h:Int = t:Int|])
    ]
    [ (([0], 0), ([1], 0),
      ImplGrEdge [form| h:Int = 1
                     && t:Int = 1
                     && i:Int = 2
                     && c:Int = 0|]
                 M.empty)
    , (([1], 0), ([1], 0),
      ImplGrEdge [form| c:Int < n:Int
                     && next':Arr{Int,Int} = store next:Arr{Int,Int} t:Int i:Int
                     && t':Int = i:Int
                     && i':Int = i:Int + 1
                     && c':Int = c:Int + 1|]
                 (M.fromList [(next, next'), (t, t'), (i, i'), (c, c')]))
    , (([1], 0), ([2], 0),
      ImplGrEdge [form| c:Int >= n:Int && c':Int = 0|]
                 (M.singleton c c'))
    , (([2], 0), ([2], 0),
      ImplGrEdge [form| c:Int < n:Int
                     && c':Int = c:Int + 1
                     && h':Int = select next:Arr{Int,Int} h:Int |]
                 (M.fromList [(h, h'), (c, c')]))
    , (([2], 0), ([3], 0),
      ImplGrEdge [form|c:Int >= n:Int|] M.empty)
    ]

noBackedges :: Ord i => G.Graph i e v -> G.Graph i e v
noBackedges g =
  foldr (\(i, _) -> uncurry G.delEdge i) g (G.backEdges g)

storeEdges :: ImplGr -> [((Node, Node), ImplGrEdge)]
storeEdges g =
  filter (\(_, ImplGrEdge f _) -> any (has _Store) $ universe f)
         (noBackedges g ^@.. G.iallEdges)

removeStores :: Form -> Form
removeStores = rewrite (\case
  (Eql _ :@ (Store _ _ :@ _ :@ _ :@ _) :@ _) -> Just (LBool True)
  (Eql _ :@ _ :@ (Store _ _ :@ _ :@ _ :@ _)) -> Just (LBool True)
  _       -> Nothing)

storeElimination :: ImplGr -> ImplGr
storeElimination g = foldr elim g (storeEdges g)

  where
    elim :: ((Node, Node), ImplGrEdge) -> ImplGr -> ImplGr
    elim ((n1, n2), ImplGrEdge f m) g =
      let f' = removeStores f
          g' = G.addEdge n1 n2 (ImplGrEdge f' m) g
          swpPos2 = G.reached n2 g' & G.mapIdxs (swp2 n1)
      in
      traceShow n1 $ traceShow n2 $
      G.addEdge n1 (swp2 n1 n2) (ImplGrEdge f' m) (g' `G.union` swpPos2)

    swp2 n1 (loc, inst) = (loc ++ [head $ fst n1, inst], 0)

main :: IO ()
main = do
  G.display "shape" g
  let g' = evalState (unfold (head $ G.backEdges g) g) emptySolveState
  G.display "unfolded" g'
  G.display "elim" $ storeElimination g'
  -- sol <- evalStateT (runExceptT $ step [4] g) emptySolveState
  -- case sol of
  --   Left (Failed m) -> putStrLn $ prettyShow m
  --   Left (Complete g') -> do
  --     putStrLn "Done!"
  --     G.display "shape-2" g'
  --   Right g' -> G.display "shape-2" g'
