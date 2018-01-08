module Language.Unstructured.Parser where

import qualified Data.Map as M
import           Text.Parsec
import           Text.ParserCombinators.Parsec.Char

import           Logic.Formula
import           Language.Unstructured.Unstructured

com :: CharParser st Com
com = (do
    v <- var
    op ":="
    f <- parseForm
    return (v := f))
  <|> (do
    res "jump"
    i <- integer
    return (Cond (LBool True) i))
  <|> pure (Cond (LBool False) 0) <* res "skip"
  <|> (do
    res "cond"
    f <- parens parseForm
    i <- integer
    return (Cond f i))
  <|> (do
    res "call"
    n <- ident
    args <- parens (commaSep parseForm)
    vals <- parens (commaSep var)
    return (Call n args vals))
  <|> (const Done <$> res "done")

imp :: CharParser st Imp
imp = com' `sepBy` op ";"
  where
    com' :: CharParser st (Com, [Var])
    com' = do
      c <- com
      _ <- symbol "~"
      vs <- parens (commaSep var)
      return (c, vs)

proc :: CharParser st (ProcName, ([Var], [Var], Imp))
proc = do
  n <- ident
  inps <- parens (commaSep var)
  outs <- parens (commaSep var)
  op "="
  i <- braces imp
  return (n, (inps, outs, i))

program :: CharParser st Program
program = do
  n <- ident
  ps <- many proc
  return (Program n (M.fromList ps))
