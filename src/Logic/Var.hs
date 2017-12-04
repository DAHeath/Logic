{-# LANGUAGE TemplateHaskell, DeriveFunctor, DeriveTraversable #-}
module Logic.Var where

import           Control.Lens

import           Data.Data (Data)
import           Data.Data.Lens (biplate)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Text.Prettyprint.Doc

import           Logic.Type (Type, Typed)
import qualified Logic.Type as T
import           Logic.Name

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
  pretty (LocPair i j) = pretty "{" <> pretty i <> pretty "," <> pretty j <> pretty "}"
  pretty Terminus = pretty "END"

data Var n
  = Bound Integer Type
  | Free n Type
  deriving (Show, Read, Eq, Ord, Data, Functor, Foldable, Traversable)
makePrisms ''Var

instance Typed (Var n)
  where typeOf (Bound _ t) = t
        typeOf (Free _ t) = t

instance Name n => Pretty (Var n)
  where pretty = pretty . varName

-- | A name for the variable. If the variable is bound, it is a textual
-- representation of the index. Otherwise, it is just the variable name.
varName :: Name n => Var n -> String
varName (Bound i _) = "!" ++ show i
varName (Free n _) = name # n

-- | A traversal which targets all of the variables in a given expression.
vars :: (Name n, Data a) => Traversal' a (Var n)
vars = biplate

-- | Perform substitution over the variables in the expression. If a given
-- variable does not appear in the mapping, it is left untouched.
subst :: (Name n, Data a) => Map (Var n) (Var n) -> a -> a
subst m = over vars (\v -> M.findWithDefault v v m)

-- | The set of all variables in the expression.
varSet :: (Name n, Data a) => a -> Set (Var n)
varSet x = S.fromList (x ^.. vars)

-- | Replace the variables in the structure by bound variables if they are in the list.
abstract :: (Name n, Data a) => [Var n] -> a -> a
abstract vs f =
  let m = foldl (\(n, m') v -> (n + 1, M.insert v (Bound n (T.typeOf v)) m')) (0, M.empty) vs
  in subst (snd m) f

-- | Replace bound variables in the structure by those in the list.
instantiate :: (Name n, Data a) => [Var n] -> a -> a
instantiate vs =
  let ts = map T.typeOf vs
      bs = zipWith Bound [0..] ts
      m = M.fromList (zip bs vs)
  in subst m
