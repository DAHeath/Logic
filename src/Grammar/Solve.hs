module Grammar.Solve where

import Grammar.Grammar
import Grammar.Inductive
import Grammar.Interpolate
import Grammar.Unwind

import Data.Map (Map)

import Logic.Formula

solve :: Grammar -> Form -> IO (Either Model (Map Symbol Form))
solve g f = loop ([], g)
  where
    loop (clones, g) = do
      res <- interpolate g f
      case res of
        Left e -> return (Left e)
        Right m -> do
          ind <- isInductive clones g m
          if ind
          then return (Right m)
          else loop (unwind (clones, g))


