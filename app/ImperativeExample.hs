{-# LANGUAGE QuasiQuotes #-}
import           Control.Monad.State

import qualified Data.Map as M
import           Data.Optic.Graph
import           Data.Optic.Graph.Extras

import qualified Logic.Type as T
import           Logic.Formula
import           Logic.Formula.Parser
import           Logic.Var
import           Language.Imperative

x, s :: Var
x = Free "x" T.Int
s = Free "s" T.Int

assS, assX :: Comm
assS = Ass s (Expr [form|s:Int + 1|])
assX = Ass x (Expr [form|x:Int + 1|])

cond :: Form
cond = [form|x:Int < n:Int|]

justBranch :: Comm
justBranch =
  Case cond
    assX
    (Seq assX assS)

branch :: Comm
branch =
  Seq
    (Case cond
      loop
      assS)
    assX

loop :: Comm
loop =
  Loop cond (
    -- Seq
    --   jumpy
    Seq assS assS)

test :: Comm
test =
  Seq
    (Seq
      (Ass x (Expr [form|0|]))
      (Seq loop loop))
  (Ass x (Expr [form|5|]))

jumpy :: Comm
jumpy =
  Seq
    assX
    (Case cond
      (Lbl 0 (Seq assS (Seq assS (Jump 0))))
      assS)

main :: IO ()
main =
  let g = commGraph test
      b = head $ backEdges g
      g' = unfold b g
  in do display "original" g
        display "unfolded" (emap (fst . semantics) g')
