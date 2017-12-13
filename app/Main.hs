module Main where

import EquivalenceExample
import SafetyExample
import KeyExample

main :: IO ()
main = do
  arg <- getLine
  case arg of
    "equiv" -> EquivalenceExample.example
    "safety" -> SafetyExample.example
    "key" -> KeyExample.example
    _ -> putStrLn "please provide a valid argument"
