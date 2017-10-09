{-# LANGUAGE DeriveDataTypeable, LambdaCase, RankNTypes #-}
module Logic.Var where

import           Control.Lens

import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S

import           Logic.Type (Type, Typed)
import qualified Logic.Type as T

import           Text.PrettyPrint.HughesPJClass (Pretty, pPrint)
import qualified Text.PrettyPrint.HughesPJClass as PP

type Name = String

data Var
  = Bound Int Type
  | Free Name Type
  deriving (Show, Read, Eq, Ord, Data)

varName :: Var -> Name
varName (Bound i _) = show i
varName (Free n _) = n

instance Typed Var
  where typeOf (Bound _ t) = t
        typeOf (Free _ t) = t

instance Pretty Var
  where pPrint (Bound n _) = PP.text ("!" ++ show n ++ ":")
        pPrint (Free  n _) = PP.text (n ++ ":")

-- | A structure which contains variables is `variadic`. This allows finding
-- the variables in the structure and substituting them for others.
class Variadic a where
  vars :: Traversal' a Var

-- | A variable is trivially variadic.
instance Variadic Var where
  vars _ = pure

-- | A list of variadic elements is variadic.
instance Variadic a => Variadic [a] where
  vars = traverse . vars

subst :: Variadic a => Map Var Var -> a -> a
subst m = over vars (\v -> M.findWithDefault v v m)

getVars :: Variadic a => a -> Set Var
getVars x = S.fromList (x ^.. vars)

-- | Given a set of used variables and a target variable, generate a new variable
-- which is not in the set and which resembles the target by appending a natural
-- number which is as close to 0 as possible.
fresh :: Set Var -> Var -> Var
fresh s = \case
  Free n t -> tryFree n 0 t
  Bound n t -> tryBound n t
  where
    tryFree :: Name -> Int -> Type -> Var
    tryFree n c t = let v' = Free (n ++ show c) t
                    in if v' `elem` s then tryFree n (c+1) t
                       else v'
    tryBound :: Int -> Type -> Var
    tryBound n t = let v' = Bound n t
                   in if v' `elem` s then tryBound (n+1) t
                      else v'

-- | Replace the variables in the structure by bound variables if they are in the list.
abstract :: Variadic a => [Var] -> a -> a
abstract vs f =
  let m = foldl (\(n, m') v -> (n + 1, M.insert v (Bound n (T.typeOf v)) m')) (0, M.empty) vs
  in subst (snd m) f

-- | Replace bound variables in the structure by those in the list.
instantiate :: Variadic a => [Var] -> a -> a
instantiate vs f =
  let m = foldl (\(n, m') v -> (n + 1, M.insert (Bound n (T.typeOf v)) v m')) (0, M.empty) vs
  in subst (snd m) f
