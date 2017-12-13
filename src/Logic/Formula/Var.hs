module Logic.Formula.Var where

import           Control.Lens

import           Data.Data (Data)
import           Data.Data.Lens (biplate)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Text.Prettyprint.Doc
import           Data.List (intercalate)
import           Data.List.Split (splitOn)

import           Logic.Formula.Type (Type, Typed)
import qualified Logic.Formula.Type as T

import           Text.Read (readMaybe)

data Var = Var
  { _varId :: [String]
  , _varLoc :: Integer
  , _varNew :: Bool
  , _varType :: Type
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Var

instance Typed Var
  where typeOf v = v ^. varType

instance Pretty Var
  where pretty = pretty . varName

-- | A name for the variable. If the variable is bound, it is a textual
-- representation of the index. Otherwise, it is just the variable name.
varName :: Var -> String
varName (Var i l nw _) =
  (if nw then "#" else "") ++ intercalate "/" (i ++ [show $ pretty l])

parseName :: String -> ([String], Integer, Bool)
parseName n =
  let (n', b) = case n of
       '#':rest -> (rest, True)
       _ -> (n, False)
      ws = splitOn "/" n'
  in
  case readMaybe (last ws) of
    Just iden -> (init ws, iden, b)
    Nothing -> (ws, 0, b)

varForName :: String -> Type -> Var
varForName n t =
  let (i, l, nw) = parseName n
  in Var i l nw t

-- | A traversal which targets all of the variables in a given expression.
vars :: Data a => Traversal' a Var
vars = biplate

-- | Perform substitution over the variables in the expression. If a given
-- variable does not appear in the mapping, it is left untouched.
subst :: Data a => Map Var Var -> a -> a
subst m = over vars (\v -> M.findWithDefault v v m)

mapVars :: Data a => (Var -> Var) -> a -> a
mapVars = over vars

-- | The set of all variables in the expression.
varSet :: Data a => a -> Set Var
varSet x = S.fromList (x ^.. vars)

-- | Replace bound variables in the structure by those in the list.
instantiate :: Data a => [Var] -> a -> a
instantiate vs =
  let ts = map T.typeOf vs
      bs = zipWith bound [0..] ts
      m = M.fromList (zip bs vs)
  in subst m

bound :: Integer -> Type -> Var
bound i = Var ["!" ++ show i] 0 False
