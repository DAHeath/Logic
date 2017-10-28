{-# LANGUAGE QuasiQuotes #-}

import           Control.Monad (void)

import qualified Data.Optic.Graph as G
import qualified Data.Map as M

import qualified Logic.Type as T
import           Logic.Formula.Parser
import           Logic.Var
import           Logic.ImplicationGraph.Type
import           Logic.ImplicationGraph.Shape

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
g = G.fromLists
    [ ((0, 0), InstanceNode $ emptyInstance [])
    , ((1, 0), InstanceNode $ emptyInstance [h, t, i, c, n, next])
    , ((2, 0), InstanceNode $ emptyInstance [h, t, c, n, next])
    , ((3, 0), QueryNode [form|h:Int = t:Int|])
    ]
    [ ((0, 0), (1, 0),
      ImplGrEdge [form| h:Int = 1
                     && t:Int = 1
                     && i:Int = 2
                     && c:Int = 0|]
                 M.empty)
    , ((1, 0), (1, 0),
      ImplGrEdge [form| c:Int < n:Int
                     && next':Arr{Int,Int} = store next:Arr{Int,Int} t:Int i:Int
                     && t':Int = i:Int
                     && i':Int = i:Int + 1
                     && c':Int = c:Int + 1|]
                 (M.fromList [(next, next'), (t, t'), (i, i'), (c, c')]))
    , ((1, 0), (2, 0),
      ImplGrEdge [form| c:Int >= n:Int && c':Int = 0|]
                 (M.singleton c c'))
    , ((2, 0), (2, 0),
      ImplGrEdge [form| c:Int < n:Int
                     && c':Int = c:Int + 1
                     && h':Int = select next:Arr{Int,Int} h:Int |]
                 (M.fromList [(h, h'), (c, c')]))
    , ((2, 0), (3, 0),
      ImplGrEdge [form|c:Int >= n:Int|] M.empty)
    ]

main :: IO ()
main = void $ shape 999 g
