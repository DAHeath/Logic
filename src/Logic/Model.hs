module Logic.Model where

import           Control.Lens

import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M

import           Logic.Var
import           Logic.Formula

import           Text.PrettyPrint.HughesPJClass (Pretty, pPrint)
import qualified Text.PrettyPrint.HughesPJClass as PP

-- | A model is an assignment of variables to formulas.
newtype Model = Model (Map Var Form)
  deriving (Show, Eq, Ord, Data)

instance Pretty Model where
  pPrint (Model m) = PP.sep vs
    where
      vs = map (\(v, f) -> PP.fsep [pPrint v, PP.text "==>", pPrint f]) $ M.toList m

-- | Replace the variables in the expression which appear in the model by their
-- assignment.
apply :: Model -> Form -> Form
apply (Model m) = rewrite (\case
  V v -> M.lookup v m
  _ -> Nothing)
