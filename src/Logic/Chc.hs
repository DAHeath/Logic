module Logic.Chc where

import           Data.Data (Data)
import           Data.Monoid ((<>))
import qualified Data.Map as M
import           Data.Text.Prettyprint.Doc hiding ((<>))

import           Logic.Formula
import           Logic.Model
import           Logic.Var
import qualified Logic.Type as T

data Chc
  = Rule [App] Form App
  | Query [App] Form Form
  deriving (Show, Eq, Ord, Data)

data App = App { appOperator :: Var, appOperands :: [Var] }
  deriving (Show, Eq, Ord, Data)

mkApp :: Name -> [Var] -> App
mkApp n vs = App (Free [n] 0 (T.curryType (map T.typeOf vs) T.Bool)) vs

instance Formulaic Chc where
  toForm (Rule lhs phi rhs) = app2 Impl (manyAnd (map toForm lhs ++ [phi])) (toForm rhs)
  toForm (Query lhs phi goal) = app2 Impl (manyAnd (map toForm lhs ++ [phi])) goal

instance Formulaic App where
  toForm (App rel vs) = appMany (V rel) (map V vs)

chcContext :: Chc -> Form
chcContext (Rule _ ctx _) = ctx
chcContext (Query _ ctx rhs) = ctx <> mkNot rhs

chcLhs :: Chc -> [App]
chcLhs (Rule lhs _ _) = lhs
chcLhs (Query lhs _ _) = lhs

chcBindings :: Chc -> [Var]
chcBindings (Rule _ _ rhs) = appOperands rhs
chcBindings Query{} = []

predicates :: Chc -> [Var]
predicates (Rule lhs _ rhs) = map appOperator (lhs ++ [rhs])
predicates (Query lhs _ _) = map appOperator lhs

applyChc :: (App -> Form) -> Chc -> Form
applyChc f = \case
  Query lhs ctx rhs -> app2 Impl (manyAnd (ctx : map f lhs)) rhs
  Rule  lhs ctx rhs -> app2 Impl (manyAnd (ctx : map f lhs)) (f rhs)

isQuery :: Chc -> Bool
isQuery Query{} = True
isQuery _ = False

instance Pretty Chc where
  pretty (Rule as f h)  = sep (map pretty as ++ [pretty f, pretty "=>", pretty h])
  pretty (Query as f h) = sep (map pretty as ++ [pretty f, pretty "=>", pretty h])

instance Pretty App where
  pretty a = braces (sep
    (pretty (varName (appOperator a)) : map pretty (appOperands a)))

applyModelToApp :: Model -> App -> Form
applyModelToApp (Model m) (App fun vs) =
  instantiate vs ((\f -> M.findWithDefault (LBool False) f m) fun)
