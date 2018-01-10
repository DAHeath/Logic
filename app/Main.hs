{-# LANGUAGE QuasiQuotes #-}

import           Data.Text.Prettyprint.Doc
import qualified Data.Map as M

import           Formula hiding (Rule)
import           Language
import           Grammar

a0, a1, a2 :: Production
a0 = Production 0 []
a1 = Production 1 []
a2 = Production 2 []

testG :: Grammar
testG =
  Grammar
    2
    [ Rule 0 a0 [form|a=0|] []
    , Rule 1 a1 [form|b=0|] []
    , Rule 0 a0 [form|c=0|] [a0]
    , Rule 1 a1 [form|d=0|] [a1]
    , Rule 1 a2 [form|e=0|] [a0]
    , Rule 0 a2 [form|f=0|] [a1]
    , Rule 0 a2 [form|g=0|] [a2]
    , Rule 1 a2 [form|h=0|] [a2]
    ]

main :: IO ()
main =
  unstructuredJava "~/Documents/Research/logic/example/Count.class" "count(I)I"
  >>= \case
    Left e -> print e
    Right p -> do
      let g = runVocab (simplify =<< mkGrammar p)
      solve g [form|not (__RESULT__ = 11)|] >>= \case
        Left m -> print (pretty (M.toList m))
        Right m -> print (pretty (M.toList m))

testE :: (String, String) -> (String, String) -> Form -> IO ()
testE (f1, m1) (f2, m2) cond = do
  f' <- unstructuredJava f1 m1
  case f' of
    Left e -> print e
    Right f -> do
      g' <- unstructuredJava f2 m2
      case g' of
        Left e -> print e
        Right g -> testUnstructured f g cond

testUnstructured :: Program -> Program -> Form -> IO ()
testUnstructured f g cond = do
  let gr = runVocab (do
        fg <- Grammar.simplify =<< mkGrammar f
        gg <- Grammar.simplify =<< mkGrammar g
        simplify (Grammar.product fg gg))

  print (pretty gr)

  solve gr cond >>= \case
    Left e -> print (pretty (M.toList e))
    Right sol -> print (pretty (M.toList sol))

multMultAcc :: IO ()
multMultAcc =
  testE ("~/Documents/Research/logic/example/Mult.class", "mult(II)I")
       ("~/Documents/Research/logic/example/Mult.class", "mult_acc(III)I")
       [form|l/x = r/x
          && l/y = r/y
          -> r/a + l/__RESULT__ = r/__RESULT__ |]

gcd :: IO ()
gcd =
  testE ("~/Documents/Research/logic/example/CanMeasureWater.class", "gcd1(II)I")
        ("~/Documents/Research/logic/example/CanMeasureWater.class", "gcd2(II)I")
       [form|l/a = r/a
          && l/b = r/b
          && l/z = r/z
          && l/a > 0
          && l/b > 0
          -> l/__RESULT__ = r/__RESULT__|]

canMeasureWater :: IO ()
canMeasureWater =
  testE ("~/Documents/Research/logic/example/CanMeasureWater.class", "canMeasureWaterTest(III)Z")
       ("~/Documents/Research/logic/example/CanMeasureWater.class", "canMeasureWater2(III)Z")
       [form|l/x = r/x
          && l/y = r/y
          && l/z = r/z
          && l/x > 0
          && l/y > 0
          && l/z > 0
          -> l/__RESULT__ = r/__RESULT__|]


addDigits12 :: IO ()
addDigits12 =
  testE ("~/Documents/Research/logic/example/AddDigits.class", "addDigits1(I)I")
       ("~/Documents/Research/logic/example/AddDigits.class", "addDigits2(I)I")
       [form|l/n = r/num
          -> l/__RESULT__ = r/__RESULT__|]

addDigits13 :: IO ()
addDigits13 =
  testE ("~/Documents/Research/logic/example/AddDigits.class", "addDigits1(I)I")
  ("~/Documents/Research/logic/example/AddDigits.class", "addDigits3(I)I")
  [form|l/n = r/num
          -> l/__RESULT__ = r/__RESULT__|]

addDigits23 :: IO ()
addDigits23 =
  testE ("~/Documents/Research/logic/example/AddDigits.class", "addDigits2(I)I")
       ("~/Documents/Research/logic/example/AddDigits.class", "addDigits3(I)I")
       [form|l/num = r/num
          -> l/__RESULT__ = r/__RESULT__|]
