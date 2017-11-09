{-# LANGUAGE QuasiQuotes #-}

import qualified Data.Optic.Graph as G
import qualified Data.Optic.Graph.Extras as G
import qualified Data.Map as M
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

cs0 :: ImplGr Integer
cs0 = G.fromLists
  [ (0, emptyInst [])
  , (1, emptyInst [n, r])
  , (2, emptyInst [n, r, s, p, i])
  , (3, emptyInst [n, r])
  ]
  [ (0, 1, Edge [form|r:Int = 0|] M.empty)
  , (1, 3, Edge [form|n:Int <= 1 && r':Int = 1|] (M.fromList [(r, r')]))
  , (1, 2, Edge [form|n:Int > 1 && s:Int = 2 && p:Int = 1 && i:Int = 2|] M.empty)
  , (2, 2, Edge [form|i:Int < n:Int
                   && i/1:Int = i:Int+1
                   && s/1:Int = s:Int + p:Int
                   && p/1:Int = s:Int |] (M.fromList [(i, i'), (s, s'), (p, p')]))
  , (2, 3 , Edge [form|i:Int >= n:Int && r/1:Int = s:Int|] (M.fromList [(r, r')]))
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

cs1 :: ImplGr Integer
cs1 = G.fromLists
  [ (0, emptyInst [])
  , (1, emptyInst [m, x])
  , (2, emptyInst [m, x, c1, c2, j])
  , (3, emptyInst [m, x])
  ]
  [ (0, 1, Edge [form|x:Int = 0|] M.empty)
  , (1, 3, Edge [form|m:Int <= 1 && x':Int = 1|] (M.fromList [(x, x')]))
  , (1, 2, Edge [form|m:Int > 1 && c1:Int = 1 && c2:Int = 1 && j:Int = 2|] M.empty)
  , (2, 2, Edge [form|j:Int <= m:Int
                   && j':Int = j:Int+1
                   && c2':Int = c2:Int + c1:Int
                   && c1':Int = c2:Int |]
           (M.fromList [(j, j'), (c1, c1'), (c2, c2')]))
  , (2, 3, Edge [form|j:Int > m:Int && x':Int = c2:Int|] (M.fromList [(x, x')]))
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

ad0 :: ImplGr Integer
ad0 = G.fromLists
  [ (0, emptyInst [])
  , (1, emptyInst [n, r])
  ]
  [ (0, 1, Edge [form|r:Int = n:Int - 9 * ((n:Int - 1) / 9)|] M.empty) ]

ad1 :: ImplGr Integer
ad1 = G.fromLists
  [ (0, emptyInst [])
  , (1, emptyInst [m, x])
  , (2, emptyInst [m, x])
  ]
  [ (0, 1, Edge [form|x:Int = m:Int|] M.empty)
  , (1, 1, Edge [form|x:Int > 9 && x/1:Int = x:Int / 10 + x:Int % 10|] (M.fromList [(x, x')]))
  , (1, 2, Edge [form|x:Int <= 9|] M.empty)
  ]

-- main :: IO ()
-- main = do
--   sol <- solve 3 3 [form|n:Int = m:Int -> x:Int = r:Int|] cs0 cs1
--   case sol of
--     Left e -> print (pretty e)
--     Right m ->
--       G.display "sol" m

main :: IO ()
main = do
  sol <- solve 1 2 [form|n:Int > 0 && n:Int = m:Int -> x:Int = r:Int|] ad0 ad1
  case sol of
    Left e -> print (pretty e)
    Right m ->
      G.display "sol" m
