{-# LANGUAGE QuasiQuotes #-}

import Control.Monad.Except
import Logic.Chc
import Logic.Solver.Z3
import Logic.Formula.Parser
import Data.Text.Prettyprint.Doc

-- test :: [Chc] -> IO ()
-- test t = do
--   sol <- liftIO (runExceptT (solveChc t))
--   case sol of
--     Left f -> do putStrLn "counterexample"
--                  print (pretty f)
--     Right m -> do putStrLn "solution"
--                   print (pretty m)

main :: IO ()
main = undefined

-- test1, test2 :: [Chc]
-- test1 = [chc| i:Int = 0 => {r i:Int}
--               {r i:Int} i':Int = i:Int + 2 && i:Int < n:Int => {r i':Int}
--               {r i:Int} i:Int >= n:Int => not (i:Int = 41) |]

-- test2 = [chc|                                 x:Int = y:Int     => {p x:Int y:Int}
--               {p x:Int y:Int} {p y:Int z:Int}                   => {q x:Int z:Int}
--               {p x:Int y:Int}                 z:Int = y:Int + 1 => {p x:Int z:Int }
--               {q x:Int z:Int}                                   => x:Int <= z:Int |]
