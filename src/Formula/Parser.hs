{-# LANGUAGE TemplateHaskell #-}
module Formula.Parser where

import           Control.Lens hiding (op)

import           Data.Data (Data)
import           Data.Generics (extQ)

import           Text.Parsec
import           Text.ParserCombinators.Parsec.Char
import qualified Text.Parsec.Token as T
import           Text.Parsec.Language (emptyDef)

import qualified Language.Haskell.TH as TH
import           Language.Haskell.TH.Quote

import           Formula.Type (Type)
import qualified Formula.Type as T
import           Formula.Expr
import           Formula.Var
import           Formula.Chc

lexeme :: Stream s m Char => ParsecT s u m b -> ParsecT s u m b
lexeme p = do { x <- p; spaces; return x  }

parseExpr :: CharParser st Expr
parseExpr = ex1

ex1 :: CharParser st Expr
ex1 = ex2 `chainl1` impop

ex2 :: CharParser st Expr
ex2 = ex3 `chainl1` (op "||" >> return (\x y -> manyOr [x, y]))

ex3 :: CharParser st Expr
ex3 = ex4 `chainl1` (op "&&" >> return (\x y -> manyAnd [x, y]))

ex4 :: CharParser st Expr
ex4 = ex6 `chainl1` compareop

ex6 :: CharParser st Expr
ex6 = ex7 `chainl1` addop

ex7 :: CharParser st Expr
ex7 = exInf `chainl1` mulop

exInf :: CharParser st Expr
exInf = atom

atom :: CharParser st Expr
atom = try app <|> nonapp
  where
    nonapp = parens parseExpr <|> (V <$> try var) <|> bool <|> (LInt <$> integer)
    app = (res "not"      >> (:@) Not                    <$> nonapp)
      <|> (res "if"       >> appMany (If T.Int)          <$> sequence [nonapp, nonapp, nonapp])
      <|> (res "store"    >> appMany (Store T.Int T.Int) <$> sequence [nonapp, nonapp, nonapp])
      <|> (res "select"   >> appMany (Select T.Int T.Int)<$> sequence [nonapp, nonapp])
      <|> (res "distinct" >> appMany (Distinct T.Int)    <$> many1 nonapp)
      <|> (res "and"      >> manyAnd                     <$> many1 nonapp)
      <|> (res "or"       >> manyOr                      <$> many1 nonapp)
      <|> (res "add"      >> appMany (Add T.Int)         <$> many1 nonapp)
      <|> (res "mul"      >> appMany (Mul T.Int)         <$> many1 nonapp)
      <|> (res "sub"      >> appMany (Sub T.Int)         <$> sequence [nonapp, nonapp])
      <|> (res "div"      >> appMany (Div T.Int)         <$> sequence [nonapp, nonapp])
      <|> (res "mod"      >> appMany (Mod T.Int)         <$> sequence [nonapp, nonapp])
      <|> (res "neql"     >> appMany (Nql T.Int)         <$> sequence [nonapp, nonapp])
      <|> (res "eql"      >> appMany (Eql T.Int)         <$> sequence [nonapp, nonapp])
      <|> (res "lt"       >> appMany (Lt T.Int)          <$> sequence [nonapp, nonapp])
      <|> (res "le"       >> appMany (Le T.Int)          <$> sequence [nonapp, nonapp])
      <|> (res "gt"       >> appMany (Gt T.Int)          <$> sequence [nonapp, nonapp])
      <|> (res "ge"       >> appMany (Ge T.Int)          <$> sequence [nonapp, nonapp])
      <|> (do v <- var
              args <- many1 nonapp
              return $ appMany (V v) args)

bool :: CharParser st Expr
bool = const (LBool True)  <$> res "true"
   <|> const (LBool False) <$> res "false"

typ :: CharParser st Type
typ = (do res "Arr"
          _ <- symbol "{"
          t1 <- typ
          _ <- symbol ","
          t2 <- typ
          _ <- symbol "}"
          return (T.Array t1 t2))
  <|> (res "Bool" >> return T.Bool)
  <|> (res "Int"  >> return T.Int)
  <|> (res "Real" >> return T.Real)
  <|> (res "Unit" >> return T.Unit)

var :: CharParser st Var
var = do
  i <- ident
  t <- annot
  return $ Var i t

annot :: CharParser st Type
annot = (op ":" >> typ) <|> pure T.Int

impop, compareop, mulop, addop :: CharParser st (Expr -> Expr -> Expr)

impop = (op "<->" >> return (app2 Iff))
    <|> (op "->"  >> return (app2 Impl))
    <|> (op "<-"  >> return (flip $ app2 Impl))

compareop = (op ">=" >> return (app2 $ Ge T.Int))
        <|> (op ">"  >> return (app2 $ Gt T.Int))
        <|> (op "<=" >> return (app2 $ Le T.Int))
        <|> (op "<"  >> return (app2 $ Lt T.Int))
        <|> (op "="  >> return (mkEql T.Int))

mulop = (op "*" >> return (app2 $ Mul T.Int))
    <|> (op "/" >> return (app2 $ Div T.Int))
    <|> (op "%" >> return (app2 $ Mod T.Int))

addop = (op "+" >> return (app2 $ Add T.Int))
    <|> (op "-" >> return (app2 $ Sub T.Int))

integer :: (Read i, Integral i) => CharParser st i
integer = lexeme $ do { ds <- many1 digit ; return (read ds) }

parseChc :: CharParser st [Chc]
parseChc = many parseChc'
  where
    parseChc' :: CharParser st Chc
    parseChc' = do
      (as, f) <- lhs
      op "=>"
      r <- rhs
      case r of
        Left a  -> return $ Rule as f a
        Right q -> return $ Query as f q

    lhs :: CharParser st ([App], Expr)
    lhs = (,) <$> many app <*> (try parseExpr <|> return (LBool True))

    rhs :: CharParser st (Either App Expr)
    rhs = (Left <$> app) <|> (Right <$> parseExpr)

    app :: CharParser st App
    app = braces $ do i <- ident
                      args <- many var
                      let ts = map (view varType) args
                      return $ App (Var i (T.curryType ts T.Bool)) args

promote :: Monad m => CharParser () a -> (String, Int, Int) -> String -> m a
promote par (file, line, col) s =
  case runParser p () "" s of
    Left err  -> fail $ show err
    Right e   -> return e
  where
    p = do pos <- getPosition
           setPosition $
             flip setSourceName file $
             flip setSourceLine line $
             setSourceColumn pos col
           spaces
           x <- par
           eof
           return x

expr :: QuasiQuoter
expr = QuasiQuoter { quoteExp = quoteFormExp parseExpr
                   , quotePat = quoteFormPat parseExpr
                   , quoteType = undefined
                   , quoteDec = undefined
                   }

chc :: QuasiQuoter
chc = QuasiQuoter { quoteExp = quoteFormExp parseChc
                  , quotePat = quoteFormPat parseChc
                  , quoteType = undefined
                  , quoteDec = undefined
                  }

thPos :: TH.Q (String, Int, Int)
thPos = do loc <- TH.location
           return ( TH.loc_filename loc
                  , fst (TH.loc_start loc)
                  , snd (TH.loc_start loc)
                  )


quoteFormExp :: (Data a) => CharParser () a -> String -> TH.ExpQ
quoteFormExp par s = do pos <- thPos
                        ex <- promote par pos s
                        dataToExpQ (const Nothing `extQ` metaExp) ex

metaExp :: Expr -> Maybe TH.ExpQ
metaExp (V (Var i _))
  | head i == '$' = Just [| $(TH.varE (TH.mkName (tail i))) |]
  | head i == '@' = Just [| V $ $(TH.varE (TH.mkName (tail i))) |]
metaExp _ = Nothing

quoteFormPat :: Data a => CharParser () a -> String -> TH.PatQ
quoteFormPat par s = do pos <- thPos
                        ex <- promote par pos s
                        dataToPatQ (const Nothing) ex

lexer :: T.GenTokenParser String u Identity
lexer = T.makeTokenParser (emptyDef { T.identStart = letter <|> char '_' <|> char '$' <|> char '#'
                                    , T.identLetter = alphaNum
                                    <|> char '_' <|> char '/' <|> char '$' <|> char '\'' <|> char '#' <|> char '/' <|> char '{' <|> char '}' <|> char '.'
                                    , T.reservedOpNames = [ "->" , "<-" , "<->" , "=>"
                                                          , "||"
                                                          , "&&"
                                                          , "=" , "<" , "<=" , ">" , ">="
                                                          , "+" , "-"
                                                          , "*" , "/", "%"
                                                          , "(", ")"
                                                          , ":"
                                                          , ":="
                                                          , ";"
                                                          , "~"
                                                          ]
                                    , T.reservedNames = [ "not", "distinct"
                                                        , "and", "or"
                                                        , "add", "mul"
                                                        , "def"
                                                        , "true", "false"
                                                        , "call"
                                                        , "anything"
                                                        , "cond"
                                                        , "return"
                                                        , "assert"
                                                        , "Int", "Bool", "Real", "Arr"
                                                        , "jump"
                                                        , "done"
                                                        , "skip"
                                                        ]
                                    })

res :: String -> CharParser st ()
res    = T.reserved lexer

ident :: CharParser st String
ident  = (do s <- symbol "$"
             i <- T.identifier lexer
             return (s ++ i))
     <|> (do s <- symbol "@"
             i <- T.identifier lexer
             return (s ++ i))
     <|> T.identifier lexer

op :: String -> CharParser st ()
op = T.reservedOp lexer

symbol :: String -> CharParser st String
symbol = T.symbol lexer

commaSep :: CharParser st a -> CharParser st [a]
commaSep = T.commaSep lexer

parens :: CharParser st a -> CharParser st a
parens = T.parens lexer

braces :: CharParser st a -> CharParser st a
braces = T.braces lexer
