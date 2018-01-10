{-# LANGUAGE OverloadedStrings #-}
module Language.Java where

import           Language.Language
import           Language.Parser

import           Data.Monoid ((<>))
import           Data.Text

import           Text.Parsec (ParseError, parse)
import qualified Turtle

data JavaError
  = JavaExitFailure Int String String
  | JavaParseError ParseError
  deriving (Show, Eq)

unstructuredJava :: FilePath -> String -> IO (Either JavaError Program)
unstructuredJava path sig = do
  res <- Turtle.shellStrictWithErr
    ( "parse-java print-ir -c "
    <> pack path
    <> " -m '" <> pack sig <> "'") Turtle.empty
  case res of
    (Turtle.ExitSuccess, t, _) ->
      case parse program "" (unpack t) of
        Left pe -> return (Left $ JavaParseError pe)
        Right p -> return (Right p)
    (Turtle.ExitFailure i, out, err) ->
      return (Left $ JavaExitFailure i (unpack out) (unpack err))
