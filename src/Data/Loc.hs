module Data.Loc where

import           Data.Data
import           Data.Text.Prettyprint.Doc

data Loc
  = Initial
  | Loc Integer
  | LocPair Loc Loc
  | Terminal
  deriving (Show, Read, Eq, Data, Ord)

instance Pretty Loc where
  pretty (Loc i) = pretty i
  pretty (LocPair i j) = pretty "{" <> pretty i <> pretty "." <> pretty j <> pretty "}"
  pretty Initial = pretty "START"
  pretty Terminal = pretty "END"
