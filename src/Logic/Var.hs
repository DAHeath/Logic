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

import           Logic.Type (Type, Typed)
import qualified Logic.Type as T

type Name = String

data Var
  = Bound Int Type
  | Free [String] Int Type
  deriving (Show, Read, Eq, Ord, Data)
makePrisms ''Var

instance Typed Var
  where typeOf (Bound _ t) = t
        typeOf (Free _ _ t) = t

instance Pretty Var
  where pretty = pretty . varName

-- | A name for the variable. If the variable is bound, it is a textual
-- representation of the index. Otherwise, it is just the variable name.
varName :: Var -> Name
varName (Bound i _) = "!" ++ show i
varName (Free ns i _) = case i of
  0 -> path ns
  _ -> path ns ++ "/" ++ show i
  where path = intercalate "/"

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

-- | Given a set of used variables and a target variable, generate a new variable
-- which is not in the set and which resembles the target by appending a natural
-- number which is as close to 0 as possible.
fresh :: Set Var -> Var -> Var
fresh s = \case
  Free ns i t -> tryFree ns (i + 1) t
  Bound n t -> tryBound n t
  where
    tryFree :: [String] -> Int -> Type -> Var
    tryFree ns c t = let v' = Free ns c t
                    in if v' `elem` s then tryFree ns (c + 1) t
                       else v'
    tryBound :: Int -> Type -> Var
    tryBound n t = let v' = Bound n t
                   in if v' `elem` s then tryBound (n+1) t
                      else v'

-- | Replace the variables in the structure by bound variables if they are in the list.
abstract :: Data a => [Var] -> a -> a
abstract vs f =
  let m = foldl (\(n, m') v -> (n + 1, M.insert v (Bound n (T.typeOf v)) m')) (0, M.empty) vs
  in subst (snd m) f

-- | Replace bound variables in the structure by those in the list.
instantiate :: Data a => [Var] -> a -> a
instantiate vs =
  let ts = map T.typeOf vs
      bs = zipWith Bound [0..] ts
      m = M.fromList (zip bs vs)
  in subst m

-- | Get the path of a var
varPath :: Var -> Maybe [String]
varPath = \case
  Free p _ _ -> Just p
  _ -> Nothing

-- | Get the alias count of a var
aliasCount :: Var -> Maybe Int
aliasCount = \case
  Free _ c _ -> Just c
  _ -> Nothing

-- | Increase var alias count
bumpVar :: (Int -> Int) -> Var -> Var
bumpVar f = \case
  Free p a t -> Free p (f a) t
  other -> other
