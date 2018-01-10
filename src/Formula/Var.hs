{-# LANGUAGE TemplateHaskell #-}
module Formula.Var where

import           Control.Lens

import           Data.Data (Data)
import           Data.Data.Lens (biplate)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Text.Prettyprint.Doc

import           Formula.Type

data Var = Var
  { _varName :: String
  , _varType :: Type
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Var

instance Pretty Var
  where pretty = pretty . _varName

-- | A traversal which targets all of the variables in a given expression.
vars :: Data a => Traversal' a Var
vars = biplate

-- | Perform substitution over the variables in the expression. If a given
-- variable does not appear in the mapping, it is left untouched.
subst :: Data a => Map Var Var -> a -> a
subst m = over vars (\v -> M.findWithDefault v v m)

-- | The set of all variables in the expression.
varSet :: Data a => a -> Set Var
varSet x = S.fromList (x ^.. vars)

-- | Replace bound variables in the structure by those in the list.
instantiate :: Data a => [Var] -> a -> a
instantiate vs =
  let ts = map (view varType) vs
      bs = zipWith bound [0..] ts
      m = M.fromList (zip bs vs)
  in subst m

bound :: Integer -> Type -> Var
bound i = Var ("!" ++ show i)
