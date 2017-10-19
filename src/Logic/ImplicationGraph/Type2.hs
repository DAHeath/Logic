{-# LANGUAGE DeriveDataTypeable #-}
module Logic.ImplicationGraph.Type2 where

import Data.Data

data Vert idx
  = Instance (Inst idx)
  | Query Form
  | Folded node
  deriving (Show, Read, Eq, Ord, Data)

data Inst idx
  = Base [Var] Form
  | And [idx] Inst
  | Or [[idx]] Inst
  deriving (Show, Read, Eq, Ord, Data)
