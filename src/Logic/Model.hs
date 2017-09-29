{-# LANGUAGE DeriveDataTypeable, LambdaCase #-}
module Logic.Model where

import           Logic.Formula

import           Control.Lens

import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M

import           Text.PrettyPrint.HughesPJClass (Pretty, pPrint)
import qualified Text.PrettyPrint.HughesPJClass as PP

newtype Model = Model (Map Var Form)
  deriving (Show, Eq, Ord, Data)

apply :: Model -> Form -> Form
apply (Model m) = rewrite (\case
  V v -> M.lookup v m
  _ -> Nothing)

instance Pretty Model where
  pPrint (Model m) = PP.sep vs
    where
      vs = map (\(v, f) -> PP.fsep [pPrint v, PP.text "==>", pPrint f]) $ M.toList m

