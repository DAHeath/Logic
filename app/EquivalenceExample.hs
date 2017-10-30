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

g1 :: ImplGr LinIdx
g1 = G.fromLists
  [ (LinIdx 0 0, emptyInst [])
  , (LinIdx 1 0, emptyInst [n, r])
  , (LinIdx 2 0, emptyInst [n, r, s, p, i])
  , (LinIdx 3 0, emptyInst [n, r])
  ]
  [ (LinIdx 0 0, LinIdx 1 0, Edge [form|r:Int = 0|] M.empty)
  , (LinIdx 1 0, LinIdx 3 0
    , Edge [form|n:Int <= 1 && r':Int = 1|] (M.fromList [(r, r')]))
  , (LinIdx 1 0, LinIdx 2 0
    , Edge [form|n:Int > 1 && s:Int = 2 && p:Int = 1 && i:Int = 2|] M.empty)
  , (LinIdx 2 0, LinIdx 2 0
    , Edge [form|i:Int < n:Int
              && i':Int = i:Int+1
              && s':Int = s:Int + p:Int
              && p':Int = s:Int |] (M.fromList [(i, i'), (s, s'), (p, p')]))
  , (LinIdx 2 0, LinIdx 3 0
    , Edge [form|i:Int >= n:Int && r':Int = s:Int|] (M.fromList [(r, r')]))
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

g2 :: ImplGr LinIdx
g2 = G.fromLists
  [ (LinIdx 0 0, emptyInst [])
  , (LinIdx 1 0, emptyInst [m, x])
  , (LinIdx 2 0, emptyInst [m, x, c1, c2, j])
  , (LinIdx 3 0, emptyInst [m, x])
  ]
  [ (LinIdx 0 0, LinIdx 1 0, Edge [form|x:Int = 0|] M.empty)
  , (LinIdx 1 0, LinIdx 3 0
    , Edge [form|m:Int <= 1 && x':Int = 1|] (M.fromList [(x, x')]))
  , (LinIdx 1 0, LinIdx 2 0
    , Edge [form|m:Int > 1 && c1:Int = 1 && c2:Int = 1 && j:Int = 2|] M.empty)
  , (LinIdx 2 0, LinIdx 2 0
    , Edge [form|j:Int <= m:Int
              && j':Int = j:Int+1
              && c2':Int = c2:Int + c1:Int
              && c1':Int = c2:Int |]
           (M.fromList [(j, j'), (c1, c1'), (c2, c2')]))
  , (LinIdx 2 0, LinIdx 3 0
    , Edge [form|j:Int > m:Int && x':Int = c2:Int|] (M.fromList [(x, x')]))
  ]

x   = Free "x" T.Int
x'  = Free "x'" T.Int
c1  = Free "c1" T.Int
c1' = Free "c1'" T.Int
m   = Free "m" T.Int
c2  = Free "c2" T.Int
c2' = Free "c2'" T.Int
j   = Free "j" T.Int
j'  = Free "j'" T.Int

r  = Free "r" T.Int
r' = Free "r'" T.Int
s  = Free "s" T.Int
s' = Free "s'" T.Int
n  = Free "n" T.Int
p  = Free "p" T.Int
p' = Free "p'" T.Int
i  = Free "i" T.Int
i' = Free "i'" T.Int


main :: IO ()
main = do
  sol <- equivalence [(n, m)] [(x, r)] (PIdx (LinIdx 3 0) (LinIdx 3 0)) g1 g2
  case sol of
    Left e -> print (pretty e)
    Right m -> print m
