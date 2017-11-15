{-# LANGUAGE TemplateHaskell #-}
module Logic.Formula.Generalizer where

import Control.Monad.State
import Control.Lens
import Logic.Var
import Logic.Formula
import Data.Data (Data)

data RelationSymbol
  = REql
  | RLe
  | RGe
  | RLt
  | RGt
  deriving (Show, Read, Eq, Ord, Data)

data RelationContent
  = RVar Var
  | RConst Integer
  deriving (Show, Read, Eq, Ord, Data)

-- | A relation is some atomic constraint involving different variables and constants.
data Relation = Relation
  { _symbol :: RelationSymbol
  , _lhs :: [RelationContent]
  , _rhs :: [RelationContent]
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Relation

reverseRelation :: Relation -> Relation
reverseRelation (Relation sym lhs rhs) = Relation (reverseSymbol sym) rhs lhs

reverseSymbol :: RelationSymbol -> RelationSymbol
reverseSymbol = \case
  REql -> REql
  RLe  -> RGe
  RGe  -> RLe
  RLt  -> RGt
  RGt  -> RLt

constantRel :: Relation -> Maybe (Var, Integer, RelationSymbol)
constantRel (Relation s l r) = case (l, r) of
  ([RVar v], [RConst c]) -> Just (v, c, s)
  _ -> Nothing

-- constantRels :: [Formula]
-- | Every formula has a constant relation for the same variable with 

generalize :: MonadIO m => [Form] -> m [[Form]]
generalize = undefined
