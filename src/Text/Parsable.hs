module Text.Parsable where

import Text.ParserCombinators.Parsec.Char

class Parsable a where
  parsable :: CharParser st a

