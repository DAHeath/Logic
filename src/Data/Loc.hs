module Data.Loc where

import           Data.Data
import           Data.Text.Prettyprint.Doc

data Loc
  = Loc Integer
  | LocPair Loc Loc
  | Initial
  | Terminal
  deriving (Show, Read, Eq, Data)

instance Ord Loc where
  Loc i        <= Loc j        = i <= j
  LocPair  i j <= LocPair  k l = i < k || (i == k && j <= l)
  LocPair  i j <= Loc k        = i < Loc k && j < Loc k
  Initial      <= _            = True
  _            <= Terminal     = True
  a            <= b            = b >= a

instance Pretty Loc where
  pretty (Loc i) = pretty i
  pretty (LocPair i j) = pretty "{" <> pretty i <> pretty "." <> pretty j <> pretty "}"
  pretty Initial = pretty "START"
  pretty Terminal = pretty "END"
