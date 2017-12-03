module Logic.Chc where

import           Control.Lens

import           Data.Data (Data)
import           Data.Monoid ((<>))
import qualified Data.Map as M
import           Data.Text.Prettyprint.Doc hiding ((<>))

import           Logic.Formula
import           Logic.Model
import           Logic.Var
import qualified Logic.Type as T

data Chc n
  = Rule [App n] (Form n) (App n)
  | Query [App n] (Form n) (Form n)
  deriving (Show, Eq, Ord, Data)

data App n = App { appOperator :: Var n, appOperands :: [Var n] }
  deriving (Show, Eq, Ord, Data)

mkApp :: Name n => String -> [Var n] -> Maybe (App n)
mkApp s vs = do
  n <- s ^? name
  return $ App (Free n (T.curryType (map T.typeOf vs) T.Bool)) vs

instance Formulaic Chc where
  toForm (Rule lhs phi rhs) = app2 Impl (manyAnd (map toForm lhs ++ [phi])) (toForm rhs)
  toForm (Query lhs phi goal) = app2 Impl (manyAnd (map toForm lhs ++ [phi])) goal

instance Formulaic App where
  toForm (App rel vs) = appMany (V rel) (map V vs)

chcContext :: Name n => Chc n -> Form n
chcContext (Rule _ ctx _) = ctx
chcContext (Query _ ctx rhs) = ctx <> mkNot rhs

chcLhs :: Chc n -> [App n]
chcLhs (Rule lhs _ _) = lhs
chcLhs (Query lhs _ _) = lhs

chcBindings :: Chc n -> [Var n]
chcBindings (Rule _ _ rhs) = appOperands rhs
chcBindings Query{} = []

predicates :: Chc n -> [Var n]
predicates (Rule lhs _ rhs) = map appOperator (lhs ++ [rhs])
predicates (Query lhs _ _) = map appOperator lhs

applyChc :: Name n => (App n -> Form n) -> Chc n -> Form n
applyChc f = \case
  Query lhs ctx rhs -> app2 Impl (manyAnd (ctx : map f lhs)) rhs
  Rule  lhs ctx rhs -> app2 Impl (manyAnd (ctx : map f lhs)) (f rhs)

isQuery :: Chc n -> Bool
isQuery Query{} = True
isQuery _ = False

instance Name n => Pretty (Chc n) where
  pretty (Rule as f h)  = sep (map pretty as ++ [pretty f, pretty "=>", pretty h])
  pretty (Query as f h) = sep (map pretty as ++ [pretty f, pretty "=>", pretty h])

instance Name n => Pretty (App n) where
  pretty a = braces (sep
    (pretty (varName (appOperator a)) : map pretty (appOperands a)))

applyModelToApp :: Name n => Model n -> App n -> Form n
applyModelToApp (Model m) (App fun vs) =
  instantiate vs ((\f -> M.findWithDefault (LBool False) f m) fun)
