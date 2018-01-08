{-# LANGUAGE QuasiQuotes #-}
import           Control.Lens

import           Data.Text.Prettyprint.Doc
import           Data.Map as M

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
    0
    [ Rule a0 [form|a=0|] [a1]
    , Rule a0 [form|b=0|] [a2]
    , Rule a1 [form|c=0|] [a1]
    , Rule a1 [form|d=0|] [a2]
    , Rule a2 [form|e=0|] []
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
