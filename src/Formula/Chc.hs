module Formula.Chc where

import           Control.Lens

import           Data.Data (Data)
import           Data.Text.Prettyprint.Doc

import           Formula.Form
import           Formula.Var
import qualified Formula.Type as T

data Chc
  = Rule [App] Form App
  | Query [App] Form Form
  deriving (Show, Eq, Ord, Data)

data App = App Var [Var]
  deriving (Show, Eq, Ord, Data)

mkApp :: String -> [Var] -> App
mkApp n vs = App (Var n (T.curryType (map (view varType) vs) T.Bool)) vs

chcForm :: Chc -> Form
chcForm (Rule lhs phi rhs) = app2 Impl (manyAnd (map appForm lhs ++ [phi])) (appForm rhs)
chcForm (Query lhs phi goal) = app2 Impl (manyAnd (map appForm lhs ++ [phi])) goal

appForm :: App -> Form
appForm (App rel vs) = appMany (V rel) (map V vs)

isQuery :: Chc -> Bool
isQuery Query{} = True
isQuery _ = False

instance Pretty Chc where
  pretty (Rule as f h)  = sep (map pretty as ++ [pretty f, pretty "=>", pretty h])
  pretty (Query as f h) = sep (map pretty as ++ [pretty f, pretty "=>", pretty h])

instance Pretty App where
  pretty (App oper args) = braces (sep
    (pretty (oper ^. varName) : map pretty args))
