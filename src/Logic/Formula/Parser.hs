{-# LANGUAGE TemplateHaskell #-}
module Logic.Formula.Parser where

import           Control.Lens hiding (op)

import           Data.Data (Data)
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
import           Logic.Name
import           Logic.Chc

lexeme :: Stream s m Char => ParsecT s u m b -> ParsecT s u m b
lexeme p = do { x <- p; spaces; return x  }

parseForm :: Name n => CharParser st (Form n)
parseForm = ex1

ex1 :: Name n => CharParser st (Form n)
ex1 = ex2 `chainl1` impop

ex2 :: Name n => CharParser st (Form n)
ex2 = ex3 `chainl1` (op "||" >> return (\x y -> manyOr [x, y]))

ex3 :: Name n => CharParser st (Form n)
ex3 = ex4 `chainl1` (op "&&" >> return (\x y -> manyAnd [x, y]))

ex4 :: Name n => CharParser st (Form n)
ex4 = ex6 `chainl1` compareop

ex6 :: Name n => CharParser st (Form n)
ex6 = ex7 `chainl1` addop

ex7 :: Name n => CharParser st (Form n)
ex7 = exInf `chainl1` mulop

exInf :: Name n => CharParser st (Form n)
exInf = atom

atom :: Name n => CharParser st (Form n)
atom = try app <|> nonapp
  where
    nonapp = parens parseForm <|> (V <$> try var) <|> bool <|> integer
    app = (res "not"      >> (:@) Not                    <$> nonapp)
      <|> (res "if"       >> appMany (If T.Int)          <$> sequence [nonapp, nonapp, nonapp])
      <|> (res "store"    >> appMany (Store T.Int T.Int) <$> sequence [nonapp, nonapp, nonapp])
      <|> (res "select"   >> appMany (Select T.Int T.Int)<$> sequence [nonapp, nonapp])
      <|> (res "distinct" >> appMany (Distinct T.Int)    <$> many1 nonapp)
      <|> (res "and"      >> manyAnd                     <$> many1 nonapp)
      <|> (res "or"       >> manyOr                      <$> many1 nonapp)
      <|> (res "add"      >> appMany (Add T.Int)         <$> many1 nonapp)
      <|> (res "mul"      >> appMany (Mul T.Int)         <$> many1 nonapp)
      <|> (do n <- pName
              op ":"
              t <- typ
              args <- many1 nonapp
              let ts = map T.typeOf args
              return $ appMany (V $ Free n (T.curryType ts t)) args)

pName :: Name n => CharParser st n
pName = do
  i <- ident
  maybe (fail ("invalid identifier " ++ i)) return (i ^? name)

bool :: CharParser st (Form n)
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

var :: Name n => CharParser st (Var n)
var = do
  i <- ident
  op ":"
  t <- typ
  case i ^? name of
    Nothing -> fail ("invalid identifier " ++ i)
    Just n -> return $ Free n t

impop, compareop, mulop, addop :: Name n => CharParser st (Form n -> Form n -> Form n)

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

integer :: Name n => CharParser st (Form n)
integer = lexeme $ do { ds <- many1 digit ; return $ LInt (read ds) }

parseChc :: Name n => CharParser st [Chc n]
parseChc = many parseChc'
  where
    parseChc' :: Name n => CharParser st (Chc n)
    parseChc' = do
      (as, f) <- lhs
      op "=>"
      r <- rhs
      case r of
        Left a  -> return $ Rule as f a
        Right q -> return $ Query as f q

    lhs :: Name n => CharParser st ([App n], Form n)
    lhs = (,) <$> many app <*> (try parseForm <|> return (LBool True))

    rhs :: Name n => CharParser st (Either (App n) (Form n))
    rhs = (Left <$> app) <|> (Right <$> parseForm)

    app :: Name n => CharParser st (App n)
    app = braces $ do n <- pName
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
form = QuasiQuoter { quoteExp = quoteFormExp (parseForm :: CharParser st (Form BasicName))
                   , quotePat = quoteFormPat (parseForm :: CharParser st (Form BasicName))
                   , quoteType = undefined
                   , quoteDec = undefined
                   }

chc :: QuasiQuoter
chc = QuasiQuoter { quoteExp = quoteFormExp (parseChc :: CharParser st [Chc BasicName])
                  , quotePat = quoteFormPat (parseChc :: CharParser st [Chc BasicName])
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

metaExp :: Form BasicName -> Maybe TH.ExpQ
metaExp (V (Free n _))
  | head (name # n) == '$' = Just [| $(TH.varE (TH.mkName (tail $ name # n))) |]
  | head (name # n) == '@' = Just [| V $ $(TH.varE (TH.mkName (tail $ name # n))) |]
metaExp _ = Nothing

quoteFormPat :: Data a => CharParser () a -> String -> TH.PatQ
quoteFormPat par s = do pos <- thPos
                        ex <- promote par pos s
                        dataToPatQ (const Nothing) ex

lexer :: T.GenTokenParser String u Identity
lexer = T.makeTokenParser (emptyDef { T.identStart = letter <|> char '_' <|> char '$' <|> char '#'
                                    , T.identLetter = alphaNum
                                                  <|> char '_' <|> char '/' <|> char '$' <|> char '\'' <|> char '#' <|> char '/'
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
                                                        , "Int", "Bool", "Real", "Arr"
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
