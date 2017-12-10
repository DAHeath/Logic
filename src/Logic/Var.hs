{-# LANGUAGE TemplateHaskell #-}
module Logic.Var where

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

import           Logic.Type (Type, Typed)
import qualified Logic.Type as T

import           Text.Read (readMaybe)

data Loc
  = Loc Integer
  | LocPair Loc Loc
  | Terminus
  deriving (Show, Read, Eq, Data)

instance Ord Loc where
  Loc i        <= Loc j        = i <= j
  LocPair  i j <= LocPair  k l = i < k || (i == k && j <= l)
  LocPair  i j <= Loc k        = i < Loc k && j < Loc k
  LocPair _ _  <= a            = True
  a            <= Terminus     = True
  a            <= b            = b >= a

instance Pretty Loc where
  pretty (Loc i) = pretty i
  pretty (LocPair i j) = pretty "{" <> pretty i <> pretty "." <> pretty j <> pretty "}"
  pretty Terminus = pretty "END"

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
    Just n  -> (init ws, n, b)
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
bound i t = Var ["!" ++ show i] 0 False t
