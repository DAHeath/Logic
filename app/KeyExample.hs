{-# LANGUAGE QuasiQuotes #-}
module KeyExample where

import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Graph.Extras as G
import           Data.Text.Prettyprint.Doc
import           Data.Functor.Identity

import           Logic.Formula as F
import           Logic.ImplicationGraph
import           Logic.Solver.Equivalence

import           Language.Structured

p, s, n, m, a, r, x, y, x', y', z :: Var
p = Var ["p"] 0 False F.Int
s = Var ["s"] 0 False F.Int
n = Var ["n"] 0 False F.Int
m = Var ["m"] 0 False F.Int
a = Var ["a"] 0 False F.Int
r = Var ["r"] 0 False F.Int
x = Var ["x"] 0 False F.Int
y = Var ["y"] 0 False F.Int
x' = Var ["x'"] 0 False F.Int
y' = Var ["y'"] 0 False F.Int
z = Var ["z"] 0 False F.Int

-- int f(int n) {
--   sum = 0;
--   while (n>0){
--     sum = sum+n
--     n --;
--   }
--   return sum
-- }
f :: Graph Loc (Identity Form) Inst
f = singleNonRec
  [ (s := [form|0|], [p,s,n])
  , (n := [form|p|], [p,s,n])
  , ( While [form|n > 0|]
        [ (s := [form|s + n|], [p,s,n])
        , (n := [form|n - 1|], [p,s,n])
        ]
    , [p,s,n])
  ]

-- int g(int n,int acc){
--   if (n<=0){return acc}
--     else{
--        return g(n-1,acc+n)
--        }
--        }
g :: Graph Loc (Identity Form) Inst
g = singleProc "g" [m, a] [r]
  [ (Br [form|m <= 0|]
      [ (r := [form|a|], [m, a, r]) ]
      [ (Call "g" [ [form|m - 1|], [form|a + m|] ] [r], [m, a, r]) ]
    , [m, a, r])
  ]

h :: Graph Loc (Identity Form) Inst
h = singleProc "h" [x] [y]
  [ (Br [form|x <= 0|]
      [ (y := [form|0|], [x, y]) ]
      [ (Call "h" [ [form|x - 1|] ] [y], [x, y])
      , (y := [form|y+x|], [x, y])
      ]
    , [x, y])
  ]

h' :: Graph Loc (Identity Form) Inst
h' = singleProc "h" [x'] [y']
  [ (Br [form|x' <= 0|]
      [ (y' := [form|0|], [x', y']) ]
      [ (Call "h" [ [form|x' - 1|] ] [y'], [x', y'])
      , (z := [form|0|], [x',y',z])
      , (While [form|z < x'|]
          [ (y' := [form|y'+1|], [x',y',z])
          , (z  := [form|z+1|], [x',y',z])
          ], [x',y',z])]
    , [x', y'])
  ]

example :: IO ()
example = do
  -- G.display "f" f
  G.display "h" h
  G.display "h2" h'
  -- sol <- solve [form|p = m -> (s + a = r)|] f g
  -- sol <- solve [form|x = m -> (y + a = r)|] g h
  -- sol <- solve [form|x = p -> (y = s)|] f h
  sol <- solve [form|x = x' -> y = y'|] h h'
  case sol of
    Left e -> print (pretty e)
    Right sol' ->
      G.display "sol" sol'
