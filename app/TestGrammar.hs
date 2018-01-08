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
      let (start, g) = runVocab (do
            (start, rs) <- mkGrammar p
            (,) start <$> simplify start rs)
      -- mapM_ (print . pretty) g
      mapM_ (print . pretty) (nonrecursive start $ unwind start g)

main :: IO ()
main =
  test ("~/Documents/Research/logic/example/Mult.class", "mult(II)I")
