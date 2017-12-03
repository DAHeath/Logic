{-# LANGUAGE TemplateHaskell #-}
module Logic.Var where

import           Control.Lens

import           Data.Typeable (Typeable)
import           Data.Data (Data)
import           Data.Data.Lens (biplate)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Maybe (fromJust)
import           Data.Text.Prettyprint.Doc
import           Data.List (intercalate)
import           Data.List.Split (splitOn)

import           Logic.Type (Type, Typed)
import qualified Logic.Type as T

import           Text.Read (readMaybe)

class (Typeable a, Data a, Ord a) => Name a where
  name :: Prism' String a
  fresh :: Set a -> a -> a

instance Name Integer where
  name = _Show
  fresh s n = if n+1 `elem` s then fresh s (n+1) else n+1

data Counted = Counted [String] Integer
  deriving (Show, Read, Eq, Ord, Data)

instance Name Counted where
  name = prism' out inc
    where
      inc s =
        let ws = splitOn "/" s
        in Just $ case readMaybe (last ws) of
          Nothing -> Counted ws 0
          Just num -> Counted (init ws) num
      out (Counted ns i) =
        case i of
          0 -> path ns
          _ -> path ns ++ "/" ++ show i
          where path = intercalate "/"
  fresh s c@(Counted n i) =
    if c `elem` s
    then fresh s (Counted n (i+1))
    else c

data Var n
  = Bound Integer Type
  | Free n Type
  deriving (Show, Read, Eq, Ord, Data)
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

-- | Given a set of used variables and a target variable, generate a new variable
-- which is not in the set and which resembles the target by appending a natural
-- number which is as close to 0 as possible.
freshVar :: Name n => Set (Var n) -> Var n -> Var n
freshVar s = \case
  Free n t  -> Free  (fresh sn n) t
  Bound i t -> Bound (fresh si i) t
  where
    sn = S.map fromJust $ S.filter (has _Just) $ S.map (\x -> x ^? _Free  . _1) s
    si = S.map fromJust $ S.filter (has _Just) $ S.map (\x -> x ^? _Bound . _1) s

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

-- | Get the path of a var
varPath :: Var Counted -> Maybe [String]
varPath = \case
  Free (Counted p _) _ -> Just p
  _ -> Nothing

-- | Get the alias count of a var
aliasCount :: Var Counted -> Maybe Integer
aliasCount = \case
  Free (Counted _ c) _ -> Just c
  _ -> Nothing

-- | Increase var alias count
bumpVar :: (Integer -> Integer) -> Var Counted -> Var Counted
bumpVar f = \case
  Free (Counted p a) t -> Free (Counted p (f a)) t
  other -> other
