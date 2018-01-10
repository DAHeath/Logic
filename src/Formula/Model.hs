{-# LANGUAGE TypeFamilies #-}
module Formula.Model where

import           Control.Lens

import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Text.Prettyprint.Doc

import           Formula.Var
import           Formula.Form

-- | A model is an assignment of variables to formulas.
newtype Model = Model { _getModel :: Map Var Form }
  deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Model

instance Pretty Model where
  pretty (Model m) = sep vs
    where
      vs = map (\(v, f) -> hsep [pretty v, pretty "==>", pretty f]) $ M.toList m

-- | Replace the variables in the expression which appear in the model by their
-- assignment.
apply :: Model -> Form -> Form
apply (Model m) = rewrite (\case
  V v -> M.lookup v m
  _ -> Nothing)

type instance Index Model = Var
type instance IxValue Model = Form
instance Ixed Model
instance At Model where
  at i = getModel . at i
