{-# LANGUAGE QuasiQuotes #-}
import           Control.Lens

import           Data.Text.Prettyprint.Doc
import           Data.Map as M
import           Data.Set as S

import           Logic.Formula hiding (Rule)
import           Language.Unstructured
import           Grammar


test :: (String, String) -> IO ()
test (f1, m1) = do
  f' <- unstructuredJava f1 m1
  case f' of
    Left _ -> putStrLn "oops"
    Right p -> do
      let g = runVocab (simplify =<< mkGrammar p)
      let (cs, g') = unwind ([], g)
      let (cs', g'') = unwind (cs, g')
      print cs'
      mapM_ (print . pretty) (view grammarRules g'')

-- main :: IO ()
-- main =
--   test ("~/Documents/Research/logic/example/Mult.class", "mult(II)I")

a0, a1, a2 :: Production
a0 = Production 0 []
a1 = Production 1 []
a2 = Production 2 []

t = LBool True

g =
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
main = do
  r <- unstructuredJava "~/Documents/Research/logic/example/Count.class" "count(I)I"
  case r of
    Left e -> print e
    Right p -> do
      let g = runVocab (simplify =<< mkGrammar p)
      r <- solve g [form|not (__RESULT__ = 11)|]
      case r of
        Left m -> print (pretty m)
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
  print "============"
  print (pretty (snd $ unwind ([], gr)))

  solve gr cond >>= \case
    Left e -> print (pretty e)
    Right sol -> print (pretty (M.toList sol))

multMultAcc :: IO ()
multMultAcc =
  testE ("~/Documents/Research/logic/example/Mult.class", "mult(II)I")
       ("~/Documents/Research/logic/example/Mult.class", "mult_acc(III)I")
       [form|l/x = r/x
          && l/y = r/y
          -> r/a + l/__RESULT__ = r/__RESULT__ |]
