{-# LANGUAGE QuasiQuotes #-}

import           Data.Text.Prettyprint.Doc
import qualified Data.Map as M

import           Formula hiding (Rule)
import           Language
import           Grammar

main :: IO ()
main = multMultAcc

test :: (String, String) -> (String, String) -> Expr -> IO ()
test (f1, m1) (f2, m2) cond =
  unstructuredJava f1 m1 >>= \case
    Left e -> print e
    Right f -> unstructuredJava f2 m2 >>= \case
      Left e -> print e
      Right g -> testUnstructured f g cond

testSame :: (String, String) -> Expr -> IO ()
testSame (f, m) cond = do
  Right code <- unstructuredJava f m
  testUnstructured code code cond

testUnstructured :: Program -> Program -> Expr -> IO ()
testUnstructured f g cond = do
  -- let fg = runVocab (Grammar.simplify =<< mkGrammar f)
  -- let gg = runVocab (Grammar.simplify =<< mkGrammar g)
  -- plot "left" fg
  -- plot "right" gg

  let gr = runVocab (do
        fg <- Grammar.simplify =<< mkGrammar f
        gg <- Grammar.simplify =<< mkGrammar g
        simplify (Grammar.product fg gg))

  -- plot "unwound" (snd $ unwind (unwind ([], gr)))
  -- print (pretty gr)

  solve gr cond >>= \case
    Left e -> print (pretty (M.toList e))
    Right sol -> print (pretty (M.toList sol))



--- MULTIPLICATION BENCHMARKS
-- mult x y + a = mult_acc x y a
multMultAcc :: IO ()
multMultAcc =
  test ("~/Documents/Research/logic/example/Mult.class", "mult(II)I")
       ("~/Documents/Research/logic/example/Mult.class", "mult_acc(III)I")
       [expr|l/x = r/x
          && l/y = r/y
          -> r/a + l/__RESULT__ = r/__RESULT__ |]

-- mult x y = mult_acc x y 0
multMultAcc0 :: IO ()
multMultAcc0 =
  test ("~/Documents/Research/logic/example/Mult.class", "mult(II)I")
       ("~/Documents/Research/logic/example/Mult.class", "mult_acc(III)I")
       [expr|l/x = r/x
          && l/y = r/y
          && r/a = 0
          -> l/__RESULT__ = r/__RESULT__ |]

-- mult (1 + x) y = y + mult x y
multL1 :: IO ()
multL1 =
  testSame ("~/Documents/Research/logic/example/Mult.class", "mult(II)I")
           [expr|l/x = r/x + 1
              && l/y = r/y
              -> l/__RESULT__ = l/y + r/__RESULT__ |]

-- y ≥ 0 ⇒ mult x (1 + y) = x + mult x y
multR1 :: IO ()
multR1 =
  testSame ("~/Documents/Research/logic/example/Mult.class", "mult(II)I")
           [expr|l/x = r/x
              && l/y = r/y + 1
              && r/y >= 0
              -> l/__RESULT__ = l/x + r/__RESULT__ |]

-- mult x y = mult y x
-- FAILING
multComm :: IO ()
multComm =
  testSame ("~/Documents/Research/logic/example/Mult.class", "mult(II)I")
           [expr|l/x = r/y
              && l/y = r/x
              -> l/__RESULT__ = r/__RESULT__ |]

-- mult (x + y) z = mult x z + mult y z
multDistR :: IO ()
multDistR =
  test ("~/Documents/Research/logic/example/Mult.class", "distR1(III)I")
       ("~/Documents/Research/logic/example/Mult.class", "distR2(III)I")
       [expr|l/x = r/x
          && l/y = r/y
          && l/z = r/z
          -> l/__RESULT__ = r/__RESULT__ |]

-- mult x (y + z) = mult x y + mult x z
multDistL :: IO ()
multDistL =
  test ("~/Documents/Research/logic/example/Mult.class", "distL1(III)I")
       ("~/Documents/Research/logic/example/Mult.class", "distL2(III)I")
       [expr|l/x = r/x
          && l/y = r/y
          && l/z = r/z
          -> l/__RESULT__ = r/__RESULT__ |]

multMono :: IO ()
multMono =
  testSame ("~/Documents/Research/logic/example/Mult.class", "mult(II)I")
           [expr|0 <= l/x
              && l/x <= r/x
              && 0 <= l/y
              && l/y <= r/y
              -> l/__RESULT__ <= r/__RESULT__|]

-- 0≤x1 ∧0≤y1 ≤y2 ⇒ mult x1 y1 ≤ mult x1 y2
multMono2 :: IO ()
multMono2 =
  testSame ("~/Documents/Research/logic/example/Mult.class", "mult(II)I")
           [expr|0 <= l/x
              && l/x = r/x
              && 0 <= l/y
              && l/y <= r/y
              -> l/__RESULT__ <= r/__RESULT__|]

-- 0≤x1≤x2 ∧0≤y1 ⇒ mult x1 y1 ≤ mult x2 y1
multMono3 :: IO ()
multMono3 =
  testSame ("~/Documents/Research/logic/example/Mult.class", "mult(II)I")
           [expr|0 <= l/x
              && l/x <= r/x
              && 0 <= l/y
              && l/y = r/y
              -> l/__RESULT__ <= r/__RESULT__|]

-- SUM BENCHMARKS
-- sum n + a = sum_acc n a
sumSumAcc :: IO ()
sumSumAcc =
  test ("~/Documents/Research/logic/example/Sum.class", "sum(I)I")
       ("~/Documents/Research/logic/example/Sum.class", "sum_acc(II)I")
       [expr|l/n = r/n
          -> l/__RESULT__ + r/a = r/__RESULT__|]

-- sum n = n + sum (n − 1) ?? requires n > 0?
sumSucc :: IO ()
sumSucc =
  testSame ("~/Documents/Research/logic/example/Sum.class", "sum(I)I")
           [expr|l/n > 0
              && l/n - 1 = r/n
              -> l/__RESULT__ = r/__RESULT__ + l/n|]

-- x ≤ y ⇒ sum x ≤ sum y
-- FAILING
sumMono :: IO ()
sumMono =
  testSame ("~/Documents/Research/logic/example/Sum.class", "sum(I)I")
           [expr|l/n <= r/n
              -> l/__RESULT__ <= r/__RESULT__|]

gcd :: IO ()
gcd =
  test ("~/Documents/Research/logic/example/CanMeasureWater.class", "gcd1(II)I")
       ("~/Documents/Research/logic/example/CanMeasureWater.class", "gcd2(II)I")
       [expr|l/a = r/a
          && l/b = r/b
          && l/z = r/z
          && l/a > 0
          && l/b > 0
          -> l/__RESULT__ = r/__RESULT__|]

canMeasureWater :: IO ()
canMeasureWater =
  test ("~/Documents/Research/logic/example/CanMeasureWater.class", "canMeasureWaterTest(III)Z")
       ("~/Documents/Research/logic/example/CanMeasureWater.class", "canMeasureWater2(III)Z")
       [expr|l/x = r/x
          && l/y = r/y
          && l/z = r/z
          && l/x > 0
          && l/y > 0
          && l/z > 0
          -> l/__RESULT__ = r/__RESULT__|]

-- LEETCODE BENCHMARKS
trailingZeroes :: IO ()
trailingZeroes =
  test ("~/Documents/Research/logic/example/TrailingZeroes.class", "trailingZeroes1(I)I")
       ("~/Documents/Research/logic/example/TrailingZeroes.class", "trailingZeroes2(I)I")
       [expr|l/n = r/n
          -> l/__RESULT__ = r/__RESULT__|]

addDigits12 :: IO ()
addDigits12 =
  test ("~/Documents/Research/logic/example/AddDigits.class", "addDigits1(I)I")
       ("~/Documents/Research/logic/example/AddDigits.class", "addDigits2(I)I")
       [expr|l/n = r/num
          -> l/__RESULT__ = r/__RESULT__|]

addDigits13 :: IO ()
addDigits13 =
  test ("~/Documents/Research/logic/example/AddDigits.class", "addDigits1(I)I")
       ("~/Documents/Research/logic/example/AddDigits.class", "addDigits3(I)I")
       [expr|l/n = r/num
          -> l/__RESULT__ = r/__RESULT__|]

addDigits23 :: IO ()
addDigits23 =
  test ("~/Documents/Research/logic/example/AddDigits.class", "addDigits2(I)I")
       ("~/Documents/Research/logic/example/AddDigits.class", "addDigits3(I)I")
       [expr|l/num = r/num
          -> l/__RESULT__ = r/__RESULT__|]
