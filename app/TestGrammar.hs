import           Logic.Formula
import           Data.Text.Prettyprint.Doc

import           Grammar
import           Language.Unstructured


test :: (String, String) -> IO ()
test (f1, m1) = do
  f' <- unstructuredJava f1 m1
  case f' of
    Left _ -> putStrLn "oops"
    Right p -> do
      let g = runVocab (do
            (start, rs) <- mkGrammar p
            simplify start rs)
      mapM_ (print . pretty) g

main :: IO ()
main =
  test ("~/Documents/Research/logic/example/Mult.class", "mult(II)I")
