{-# LANGUAGE QuasiQuotes #-}
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Graph.Extras as G
import           Data.Text.Prettyprint.Doc

import           Logic.Var
import           Logic.Formula.Parser
import qualified Logic.Type as T
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Equivalence

import           Language.Structured

p, s, n, m, a, r :: Var
p = Var ["p"] 0 False T.Int
s = Var ["s"] 0 False T.Int
n = Var ["n"] 0 False T.Int
m = Var ["m"] 0 False T.Int
a = Var ["a"] 0 False T.Int
r = Var ["r"] 0 False T.Int

-- int f(int n) {
--   sum = 0;
--   while (n>0){
--     sum = sum+n
--     n --;
--   }
--   return sum
-- }
f :: Graph Loc Edge Inst
f = singleNonRec
  [ (s := [form|0|], [p,s,n])
  , (n := [form|p:Int|], [p,s,n])
  , ( While [form|n:Int > 0|]
        [ (s := [form|s:Int + n:Int|], [p,s,n])
        , (n := [form|n:Int - 1|], [p,s,n])
        ]
    , [p,s,n])
  ]

-- int g(int n,int acc){
--   if (n<=0){return acc}
--     else{
--        return g(n-1,acc+n)
--        }
--        }
g :: Graph Loc Edge Inst
g = singleProc "g" [m, a] [r]
  [ (Br [form|m:Int <= 0|]
      [ (r := [form|a:Int|], [m, a, r]) ]
      [ (Call "g" [ [form|m:Int - 1|], [form|a:Int + m:Int|] ] [r], [m, a, r]) ]
    , [m, a, r])
  ]

main :: IO ()
main = do
  sol <- solve [form|p/6:Int = m/4:Int -> (s/6:Int + a/4:Int = r/4:Int)|] f g
  case sol of
    Left e -> print (pretty e)
    Right sol' ->
      G.display "sol" sol'
