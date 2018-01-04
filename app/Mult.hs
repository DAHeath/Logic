{-# LANGUAGE QuasiQuotes, ScopedTypeVariables #-}
import           Data.Text.Prettyprint.Doc
import           Data.Loc
import           Data.Functor.Identity
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Graph.Extras as G

import           Language.Unstructured
import           Language.Unstructured.Java
import           Logic.Formula as F
import           Logic.ImplicationGraph
import           Logic.Solver.Equivalence

testUnstructured :: Program -> Program -> Form -> IO ()
testUnstructured f g cond = do
  let fg = impGraph f :: Graph Loc (Identity Form) Inst
  let gg = impGraph g

  sol <- solve cond fg gg
  case sol of
    Left e -> print (pretty e)
    Right sol' ->
      G.display "sol" sol'

testSame :: (String, String) -> Form -> IO ()
testSame (f, m) cond = do
  Right code <- unstructuredJava f m
  testUnstructured code code cond

test :: (String, String) -> (String, String) -> Form -> IO ()
test (f1, m1) (f2, m2) cond = do
  Right f <- unstructuredJava f1 m1
  Right g <- unstructuredJava f2 m2
  testUnstructured f g cond

-- mult x y + a = mult acc x y a
multMultAcc :: IO ()
multMultAcc =
  test ("~/Documents/Research/logic/example/Mult.class", "mult(II)I")
       ("~/Documents/Research/logic/example/Mult.class", "mult_acc(III)I")
       [form|l/x = r/x
          && l/y = r/y
          -> r/a + l/__RESULT__ = r/__RESULT__ |]

-- mult x y = mult_acc x y 0
multMultAcc0 :: IO ()
multMultAcc0 =
  test ("~/Documents/Research/logic/example/Mult.class", "mult(II)I")
       ("~/Documents/Research/logic/example/Mult.class", "mult_acc(III)I")
       [form|l/x = r/x
          && l/y = r/y
          && r/a = 0
          -> l/__RESULT__ = r/__RESULT__ |]

-- mult (1 + x) y = y + mult x y
multL1 :: IO ()
multL1 =
  testSame ("~/Documents/Research/logic/example/Mult.class", "mult(II)I")
           [form|l/x = r/x + 1
              && l/y = r/y
              -> l/__RESULT__ = l/y + r/__RESULT__ |]


-- y ≥ 0 ⇒ mult x (1 + y) = x + mult x y
multR1 :: IO ()
multR1 =
  testSame ("~/Documents/Research/logic/example/Mult.class", "mult(II)I")
           [form|l/x = r/x
              && l/y = r/y + 1
              && r/y >= 0
              -> l/__RESULT__ = l/x + r/__RESULT__ |]


-- mult x y = mult y x
multComm :: IO ()
multComm =
  testSame ("~/Documents/Research/logic/example/Mult.class", "mult(II)I")
           [form|l/x = r/y
              && l/y = r/x
              -> l/__RESULT__ = r/__RESULT__ |]

-- mult (x + y) z = mult x z + mult y z
multDistR :: IO ()
multDistR =
  test ("~/Documents/Research/logic/example/Mult.class", "distR1(III)I")
       ("~/Documents/Research/logic/example/Mult.class", "distR2(III)I")
       [form|l/x = r/x
          && l/y = r/y
          && l/z = r/z
          -> l/__RESULT__ = r/__RESULT__ |]

-- mult x (y + z) = mult x y + mult x z
multDistL :: IO ()
multDistL =
  test ("~/Documents/Research/logic/example/Mult.class", "distL1(III)I")
       ("~/Documents/Research/logic/example/Mult.class", "distL2(III)I")
       [form|l/x = r/x
          && l/y = r/y
          && l/z = r/z
          -> l/__RESULT__ = r/__RESULT__ |]

multMono :: IO ()
multMono =
  testSame ("~/Documents/Research/logic/example/Mult.class", "mult(II)I")
           [form|0 <= l/x
              && l/x <= r/x
              && 0 <= l/y
              && l/y <= r/y
              -> l/__RESULT__ <= r/__RESULT__|]
