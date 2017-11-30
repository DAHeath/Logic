{-# LANGUAGE QuasiQuotes #-}
import           Control.Lens

import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G
import qualified Data.Optic.Graph.Extras as G
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Text.Prettyprint.Doc

import           Logic.Var
import           Logic.Formula.Parser
import qualified Logic.Type as T
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Equivalence

-- public int climbStairs0(int n) {
--   int r = 0;
--   if (n <= 1) { r = 1; }
--   else {
--     int s = 2; int p = 1, c = 0;
--     for(int i = 2; i < n; i++) {
--       c = s;
--       s += p;
--       p = c;
--     }
--     r = s;
--   }
--   return r;
-- }

cs0 :: Graph Loc Edge Inst
cs0 = G.fromLists
  [ (Loc 0, emptyInst (Loc 0) [n, r])
  , (Loc 1, emptyInst (Loc 1) [n, r, s, p, i])
  , (Loc 2, emptyInst (Loc 2) [n, r])
  ]
  [ (G.HEdge S.empty (Loc 0), Edge [form|r:Int = 0|] M.empty)
  , (G.HEdge (S.singleton (Loc 0)) (Loc 2), Edge [form|n:Int <= 1 && r/1:Int = 1|] (M.fromList [(r, r')]))
  , (G.HEdge (S.singleton (Loc 0)) (Loc 1), Edge [form|n:Int > 1 && s:Int = 2 && p:Int = 1 && i:Int = 2|] M.empty)
  , (G.HEdge (S.singleton (Loc 1)) (Loc 1), Edge [form|i:Int < n:Int
                   && i/1:Int = i:Int+1
                   && s/1:Int = s:Int + p:Int
                   && p/1:Int = s:Int |] (M.fromList [(i, i'), (s, s'), (p, p')]))
  , (G.HEdge (S.singleton (Loc 1)) (Loc 2) , Edge [form|i:Int >= n:Int && r/1:Int = s:Int|] (M.fromList [(r, r')]))
  ]


-- public int climbStairs1(int m) {
--   int x = 0;
--   if(m <= 1) { x = 1; }
--   else {
--     int c1 = 1;
--     int c2 = 1;
--     for (int j = 2; j <= m; j++) {
--       int temp = c2;
--       c2 = temp + c1;
--       c1 = temp;
--     }
--     x = c2;
--   }
--   return x;
-- }

cs1 :: Graph Loc Edge Inst
cs1 = G.fromLists
  [ (Loc 0, emptyInst (Loc 0) [m, x])
  , (Loc 1, emptyInst (Loc 1) [m, x, c1, c2, j])
  , (Loc 2, emptyInst (Loc 2) [m, x])
  ]
  [ (G.HEdge S.empty (Loc 0), Edge [form|x:Int = 0|] M.empty)
  , (G.HEdge (S.singleton (Loc 0)) (Loc 2), Edge [form|m:Int <= 1 && x/1:Int = 1|] (M.fromList [(x, x')]))
  , (G.HEdge (S.singleton (Loc 0)) (Loc 1), Edge [form|m:Int > 1 && c1:Int = 1 && c2:Int = 1 && j:Int = 2|] M.empty)
  , (G.HEdge (S.singleton (Loc 1)) (Loc 1), Edge [form|j:Int <= m:Int
                   && j/1:Int = j:Int+1
                   && c2/1:Int = c2:Int + c1:Int
                   && c1/1:Int = c2:Int |]
           (M.fromList [(j, j'), (c1, c1'), (c2, c2')]))
  , (G.HEdge (S.singleton (Loc 1)) (Loc 2), Edge [form|j:Int > m:Int && x/1:Int = c2:Int|] (M.fromList [(x, x')]))
  ]

x   = Free ["x"] 0 T.Int
x'  = Free ["x"] 1 T.Int
c1  = Free ["c1"] 0 T.Int
c1' = Free ["c1"] 1 T.Int
m   = Free ["m"] 0 T.Int
c2  = Free ["c2"] 0 T.Int
c2' = Free ["c2"] 1 T.Int
j   = Free ["j"] 0 T.Int
j'  = Free ["j"] 1 T.Int

r  = Free ["r"] 0 T.Int
r' = Free ["r"] 1 T.Int
s  = Free ["s"] 0 T.Int
s' = Free ["s"] 1 T.Int
n  = Free ["n"] 0 T.Int
p  = Free ["p"] 0 T.Int
p' = Free ["p"] 1 T.Int
i  = Free ["i"] 0 T.Int
i' = Free ["i"] 1 T.Int

ad0 :: Graph Loc Edge Inst
ad0 = G.fromLists
  [ (Loc 0, emptyInst (Loc 0) [])
  , (Loc 1, emptyInst (Loc 1) [n, r]) ]
  [ (G.HEdge (S.singleton (Loc 0)) (Loc 1), Edge [form|r:Int = n:Int - 9 * ((n:Int - 1) / 9)|] M.empty) ]

ad1 :: Graph Loc Edge Inst
ad1 = G.fromLists
  [ (Loc 0, emptyInst (Loc 0) [])
  , (Loc 1, emptyInst (Loc 1) [m, x])
  , (Loc 2, emptyInst (Loc 2) [m, x])
  ]
  [ (G.HEdge (S.singleton (Loc 0)) (Loc 1), Edge [form|x:Int = m:Int|] M.empty)
  , (G.HEdge (S.singleton (Loc 1)) (Loc 1), Edge [form|x:Int > 9 && x/1:Int = x:Int / 10 + x:Int % 10|] (M.fromList [(x, x')]))
  , (G.HEdge (S.singleton (Loc 1)) (Loc 2), Edge [form|x:Int <= 9|] M.empty)
  ]

-- main :: IO ()
-- main = do
--   sol <- solve 3 3 [form|n:Int = m:Int -> x:Int = r:Int|] cs0 cs1
--   case sol of
--     Left e -> print (pretty e)
--     Right m ->
--       G.display "sol" (m ^. implGr)

main :: IO ()
main = do
  sol <- solve (Loc 1) (Loc 2) [form|n:Int > 0 && n:Int = m:Int -> x:Int = r:Int|] ad0 ad1
  case sol of
    Left e -> print (pretty e)
    Right m ->
      G.display "sol" m
