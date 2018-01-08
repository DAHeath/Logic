import           Control.Lens

import           Data.Text.Prettyprint.Doc

import           Logic.Formula
import           Language.Unstructured
import           Grammar


test :: (String, String) -> IO ()
test (f1, m1) = do
  f' <- unstructuredJava f1 m1
  case f' of
    Left _ -> putStrLn "oops"
    Right p -> do
      let g = runVocab (simplify =<< mkGrammar p)
      mapM_ (print . pretty) (view grammarRules (unwind g))

main :: IO ()
main =
  test ("~/Documents/Research/logic/example/Mult.class", "mult(II)I")
