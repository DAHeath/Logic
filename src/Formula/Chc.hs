module Formula.Chc where

import           Control.Lens

import           Data.Data (Data)
import           Data.Text.Prettyprint.Doc

import           Formula.Expr
import           Formula.Var
import qualified Formula.Type as T

data Chc
  = Rule [App] Expr App
  | Query [App] Expr Expr
  deriving (Show, Eq, Ord, Data)

data App = App Var [Var]
  deriving (Show, Eq, Ord, Data)

mkApp :: String -> [Var] -> App
mkApp n vs = App (Var n (T.curryType (map (view varType) vs) T.Bool)) vs

chcExpr :: Chc -> Expr
chcExpr (Rule lhs phi rhs) = app2 Impl (manyAnd (map appExpr lhs ++ [phi])) (appExpr rhs)
chcExpr (Query lhs phi goal) = app2 Impl (manyAnd (map appExpr lhs ++ [phi])) goal

appExpr :: App -> Expr
appExpr (App rel vs) = appMany (V rel) (map V vs)

isQuery :: Chc -> Bool
isQuery Query{} = True
isQuery _ = False

instance Pretty Chc where
  pretty (Rule as f h)  = sep (map pretty as ++ [pretty f, pretty "=>", pretty h])
  pretty (Query as f h) = sep (map pretty as ++ [pretty f, pretty "=>", pretty h])

instance Pretty App where
  pretty (App oper args) = braces (sep
    (pretty (oper ^. varName) : map pretty args))
