import qualified Data.Map as M
import           Text.Parsec
import           Text.ParserCombinators.Parsec.Char

import           Logic.Var
import           Logic.Formula.Parser
import           Language.Unstructured

com :: CharParser st Com
com = (do
    v <- var
    op ":="
    f <- parseForm
    return (v := f))
  <|> (do
    res "jump"
    i <- integer
    return (Jump i))
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
