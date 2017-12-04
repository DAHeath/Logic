module Logic.Model where

import           Control.Lens

import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Text.Prettyprint.Doc

import           Logic.Var
import           Logic.Name
import           Logic.Formula

-- | A model is an assignment of variables to formulas.
newtype Model n = Model { getModel :: Map (Var n) (Form n) }
  deriving (Show, Read, Eq, Ord, Data)

instance Name n => Pretty (Model n) where
  pretty (Model m) = sep vs
    where
      vs = map (\(v, f) -> hsep [pretty v, pretty "==>", pretty f]) $ M.toList m

-- | Replace the variables in the expression which appear in the model by their
-- assignment.
apply :: Name n => Model n -> Form n -> Form n
apply (Model m) = rewrite (\case
  V v -> M.lookup v m
  _ -> Nothing)
