module Logic.Formula.Tokens where

import           Data.Functor.Identity

import           Text.Parsec
import           Text.ParserCombinators.Parsec.Char
import qualified Text.Parsec.Token as T
import           Text.Parsec.Language (emptyDef)

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
