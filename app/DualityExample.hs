{-# LANGUAGE QuasiQuotes #-}

import Logic.Formula
import Logic.Chc
import Logic.Solver.Z3
import Logic.Solver.Duality
import Logic.Formula.Parser
import Text.PrettyPrint.HughesPJClass (prettyShow)

test :: [Chc] -> IO ()
test t = do
  sol <- solveChc t
  case sol of
    Left f -> do putStrLn "counterexample"
                 putStrLn (prettyShow f)
    Right m -> do putStrLn "solution"
                  putStrLn (prettyShow m)

testDuality :: [Chc] -> IO ()
testDuality t = do
  sol <- duality t
  case sol of
    Left f -> do putStrLn "counterexample"
                 putStrLn (prettyShow f)
    Right m -> do putStrLn "solution"
                  putStrLn (prettyShow m)

main :: IO ()
main = do
  testDuality test2

test1, test2 :: [Chc]
test1 = [chc| i:Int = 0 => {r i:Int}
              {r i:Int} i':Int = i:Int + 2 && i:Int < n:Int => {r i':Int}
              {r i:Int} i:Int >= n:Int => not (i:Int = 41) |]

test2 = [chc|                                 x:Int = y:Int     => {p x:Int y:Int}
              {p x:Int y:Int} {p y:Int z:Int}                   => {q x:Int z:Int}
              {p x:Int y:Int}                 z:Int = y:Int + 1 => {p x:Int z:Int }
              {q x:Int z:Int}                                   => x:Int <= z:Int |]
