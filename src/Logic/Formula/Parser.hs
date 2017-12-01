{-# LANGUAGE TemplateHaskell #-}
module Logic.Formula.Parser where

import           Data.Data (Data)
import           Data.Functor.Identity
import           Data.Generics (extQ)

import           Text.Parsec
import           Text.ParserCombinators.Parsec.Char
import qualified Text.Parsec.Token as T
import           Text.Parsec.Language (emptyDef)
import           Text.Parsable

import qualified Language.Haskell.TH as TH
import           Language.Haskell.TH.Quote

import           Logic.Type (Type)
import qualified Logic.Type as T
import           Logic.Formula
import           Logic.Formula.Tokens
import           Logic.Var
import           Logic.Chc

lexeme :: Stream s m Char => ParsecT s u m b -> ParsecT s u m b
lexeme p = do { x <- p; spaces; return x  }

parseForm :: (Parsable v, Eq v) => CharParser st (Form v)
parseForm = ex1

ex1 :: (Parsable v, Eq v) => CharParser st (Form v)
ex1 = ex2 `chainl1` impop

ex2 :: (Parsable v, Eq v) => CharParser st (Form v)
ex2 = ex3 `chainl1` (op "||" >> return (\x y -> manyOr [x, y]))

ex3 :: (Parsable v, Eq v) => CharParser st (Form v)
ex3 = ex4 `chainl1` (op "&&" >> return (\x y -> manyAnd [x, y]))

ex4 :: (Parsable v, Eq v) => CharParser st (Form v)
ex4 = ex6 `chainl1` compareop

ex6 :: (Parsable v, Eq v) => CharParser st (Form v)
ex6 = ex7 `chainl1` addop

ex7 :: (Parsable v, Eq v) => CharParser st (Form v)
ex7 = exInf `chainl1` mulop

exInf :: (Parsable v, Eq v) => CharParser st (Form v)
exInf = atom

atom :: (Parsable v, Eq v) => CharParser st (Form v)
atom = try app <|> nonapp
  where
    nonapp = parens parseForm <|> (V <$> try parsable) <|> bool <|> integer
    app = (res "not"      >> (:@) Not                    <$> nonapp)
      <|> (res "if"       >> appMany (If T.Int)          <$> sequence [nonapp, nonapp, nonapp])
      <|> (res "store"    >> appMany (Store T.Int T.Int) <$> sequence [nonapp, nonapp, nonapp])
      <|> (res "select"   >> appMany (Select T.Int T.Int)<$> sequence [nonapp, nonapp])
      <|> (res "distinct" >> appMany (Distinct T.Int)    <$> many1 nonapp)
      <|> (res "and"      >> manyAnd                     <$> many1 nonapp)
      <|> (res "or"       >> manyOr                      <$> many1 nonapp)
      <|> (res "add"      >> appMany (Add T.Int)         <$> many1 nonapp)
      <|> (res "mul"      >> appMany (Mul T.Int)         <$> many1 nonapp)
      <|> (do n <- parsable
              args <- many1 nonapp
              return $ appMany (V n) args)

bool :: CharParser st (Form v)
bool = const (LBool True)  <$> res "true"
   <|> const (LBool False) <$> res "false"

impop, compareop, mulop, addop
  :: Eq v
  => CharParser st (Form v -> Form v -> Form v)

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

integer :: CharParser st (Form v)
integer = lexeme $ do { ds <- many1 digit ; return $ LInt (read ds) }

parseChc :: (Eq v, Parsable v) => CharParser st [Chc v]
parseChc = many parseChc'
  where
    parseChc' :: (Eq v, Parsable v) => CharParser st (Chc v)
    parseChc' = do
      (as, f) <- lhs
      op "=>"
      r <- rhs
      case r of
        Left a  -> return $ Rule as f a
        Right q -> return $ Query as f q

    lhs :: (Eq v, Parsable v) => CharParser st ([App v], Form v)
    lhs = (,) <$> many app <*> (try parseForm <|> return (LBool True))

    rhs :: (Eq v, Parsable v) => CharParser st (Either (App v) (Form v))
    rhs = (Left <$> app) <|> (Right <$> parseForm)

    app :: (Eq v, Parsable v) => CharParser st (App v)
    app = braces $ App <$> parsable <*> many parsable

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
form = QuasiQuoter { quoteExp = quoteFormExp (parseForm :: CharParser st (Form Var))
                   , quotePat = quoteFormPat (parseForm :: CharParser st (Form Var))
                   , quoteType = undefined
                   , quoteDec = undefined
                   }

chc :: QuasiQuoter
chc = QuasiQuoter { quoteExp = quoteFormExp (parseChc :: CharParser st [Chc Var])
                  , quotePat = quoteFormPat (parseChc :: CharParser st [Chc Var])
                  , quoteType = undefined
                  , quoteDec = undefined
                  }

thPos :: TH.Q (String, Int, Int)
thPos = do loc <- TH.location
           return ( TH.loc_filename loc
                  , fst (TH.loc_start loc)
                  , snd (TH.loc_start loc)
                  )


quoteFormExp :: (Data f) => CharParser () f -> String -> TH.ExpQ
quoteFormExp par s = do pos <- thPos
                        ex <- promote par pos s
                        dataToExpQ (const Nothing `extQ` metaExp) ex

metaExp :: Form Var -> Maybe TH.ExpQ
metaExp (V v)
  | head (nameOf v) == '$' = Just [| $(TH.varE (TH.mkName (tail (nameOf v)))) |]
  | head (nameOf v) == '@' = Just [| V $ $(TH.varE (TH.mkName (tail (nameOf v)))) |]
metaExp _ = Nothing

quoteFormPat :: Data a => CharParser () a -> String -> TH.PatQ
quoteFormPat par s = do pos <- thPos
                        ex <- promote par pos s
                        dataToPatQ (const Nothing) ex
