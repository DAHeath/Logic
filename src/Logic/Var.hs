{-# LANGUAGE DeriveDataTypeable, LambdaCase #-}
module Logic.Var where

import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S

import           Logic.Type (Type, Typed)
import qualified Logic.Type as T

import           Text.PrettyPrint.HughesPJClass (Pretty, (<>), pPrint)
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
  where pPrint (Bound n t) = PP.text (show n ++ ":") <> PP.pPrint t
        pPrint (Free  n t) = PP.text (n ++ ":") <> PP.pPrint t

class Variadic a where
  vars :: a -> Set Var
  subst :: Map Var Var -> a -> a

instance Variadic Var where
  vars = S.singleton
  subst m v = M.findWithDefault v v m

instance Variadic a => Variadic [a] where
  vars = S.unions . map vars
  subst m = map (subst m)

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

abstract :: Variadic a => [Var] -> a -> a
abstract vs f =
  let m = foldl (\(n, m') v -> (n + 1, M.insert v (Bound n (T.typeOf v)) m')) (0, M.empty) vs
  in subst (snd m) f

instantiate :: Variadic a => [Var] -> a -> a
instantiate vs f =
  let m = foldl (\(n, m') v -> (n + 1, M.insert (Bound n (T.typeOf v)) v m')) (0, M.empty) vs
  in subst (snd m) f
