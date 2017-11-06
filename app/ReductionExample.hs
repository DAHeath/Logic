{-# LANGUAGE QuasiQuotes #-}
import           Data.Text.Prettyprint.Doc
import Logic.Formula
import Logic.Formula.Parser
import Logic.Solver.Z3

example :: Form
example =
  [form|a:Int = 0 || b:Int <= 1 || b:Int <= 2 || a:Int = 0|]


