{-# LANGUAGE FlexibleContexts, TemplateHaskell #-}
module Logic.Formula.Parser where

import           Data.Data (Data)
import           Data.Functor.Identity
import           Data.Generics (extQ)

import           Text.Parsec
import           Text.ParserCombinators.Parsec.Char
import qualified Text.Parsec.Token as T
import           Text.Parsec.Language (emptyDef)

import qualified Language.Haskell.TH as TH
import           Language.Haskell.TH.Quote

import           Logic.Type (Type)
import qualified Logic.Type as T
import           Logic.Formula
import           Logic.Var
import           Logic.Chc

lexeme :: Stream s m Char => ParsecT s u m b -> ParsecT s u m b
lexeme p = do { x <- p; spaces; return x  }

parseForm :: CharParser st Form
parseForm = ex1

ex1 :: CharParser st Form
ex1 = ex2 `chainl1` impop

ex2 :: CharParser st Form
ex2 = ex3 `chainl1` (op "||" >> return (\x y -> manyOr [x, y]))

ex3 :: CharParser st Form
ex3 = ex4 `chainl1` (op "&&" >> return (\x y -> manyAnd [x, y]))

ex4 :: CharParser st Form
ex4 = ex6 `chainl1` compareop

ex6 :: CharParser st Form
ex6 = ex7 `chainl1` addop

ex7 :: CharParser st Form
ex7 = exInf `chainl1` mulop

exInf :: CharParser st Form
exInf = atom

atom :: CharParser st Form
atom = try app <|> nonapp
  where
    nonapp = parens parseForm <|> (V <$> try var) <|> bool <|> integer
    app = (res "not"      >> Apply Not                <$> nonapp)
      <|> (res "if"       >> appMany (If T.Int)       <$> sequence [nonapp, nonapp, nonapp])
      <|> (res "distinct" >> appMany (Distinct T.Int) <$> many1 nonapp)
      <|> (res "and"      >> manyAnd                  <$> many1 nonapp)
      <|> (res "or"       >> manyOr                   <$> many1 nonapp)
      <|> (res "add"      >> appMany (Add T.Int)      <$> many1 nonapp)
      <|> (res "mul"      >> appMany (Mul T.Int)      <$> many1 nonapp)
      <|> (do n <- ident
              op ":"
              t <- typ
              args <- many1 nonapp
              let ts = map T.typeOf args
              return $ appMany (V $ Free n (T.curryType ts t)) args)

bool :: CharParser st Form
bool = const (LBool True)  <$> res "true"
   <|> const (LBool False) <$> res "false"

typ :: CharParser st Type
typ = (res "Bool" >> return T.Bool)
  <|> (res "Int"  >> return T.Int)
  <|> (res "Real" >> return T.Real)
  <|> (res "Unit" >> return T.Unit)

var :: CharParser st Var
var = do
  i <- ident
  op ":"
  t <- typ
  return $ Free i t

impop, compareop, mulop, addop :: CharParser st (Form -> Form -> Form)

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

integer :: CharParser st Form
integer = lexeme $ do { ds <- many1 digit ; return $ LInt (read ds) }

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

    lhs :: CharParser st ([App], Form)
    lhs = (,) <$> many app <*> (try parseForm <|> return (LBool True))

    rhs :: CharParser st (Either App Form)
    rhs = (Left <$> app) <|> (Right <$> parseForm)

    app :: CharParser st App
    app = braces $ do n <- ident
                      args <- many var
                      let ts = map T.typeOf args
                      return $ App (Free n (T.curryType ts T.Bool)) args

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

form :: QuasiQuoter
form = QuasiQuoter { quoteExp = quoteFormExp parseForm
                   , quotePat = quoteFormPat parseForm
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


quoteFormExp :: Data a => CharParser () a -> String -> TH.ExpQ
quoteFormExp par s = do pos <- thPos
                        ex <- promote par pos s
                        dataToExpQ (const Nothing `extQ` metaExp) ex

metaExp :: Form -> Maybe TH.ExpQ
metaExp (V (Free x _))
  | head x == '$' = Just [| $(TH.varE (TH.mkName (tail x))) |]
  | head x == '@' = Just [| V $ $(TH.varE (TH.mkName (tail x))) |]
metaExp _ = Nothing

quoteFormPat :: Data a => CharParser () a -> String -> TH.PatQ
quoteFormPat par s = do pos <- thPos
                        ex <- promote par pos s
                        dataToPatQ (const Nothing) ex

lexer :: T.GenTokenParser String u Identity
lexer = T.makeTokenParser (emptyDef { T.identStart = letter <|> char '_' <|> char '$'
                                    , T.identLetter = alphaNum
                                                  <|> char '_' <|> char '/' <|> char '$' <|> char '\''
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
