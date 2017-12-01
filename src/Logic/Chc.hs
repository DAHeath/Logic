module Logic.Chc where

import           Data.Data (Data)
import           Data.Monoid ((<>))
import qualified Data.Map as M
import           Data.Text.Prettyprint.Doc hiding ((<>))

import           Logic.Formula
import           Logic.Model
import           Logic.Var
import qualified Logic.Type as T

data Chc v
  = Rule [App v] (Form v) (App v)
  | Query [App v] (Form v) (Form v)
  deriving (Show, Eq, Ord, Data)

data App v = App { appOperator :: v, appOperands :: [v] }
  deriving (Show, Eq, Ord, Data)

instance Formulaic Chc where
  toForm (Rule lhs phi rhs) = app2 Impl (manyAnd (map toForm lhs ++ [phi])) (toForm rhs)
  toForm (Query lhs phi goal) = app2 Impl (manyAnd (map toForm lhs ++ [phi])) goal

instance Formulaic App where
  toForm (App rel vs) = appMany (V rel) (map V vs)

chcContext :: Eq v => Chc v -> Form v
chcContext (Rule _ ctx _) = ctx
chcContext (Query _ ctx rhs) = ctx <> mkNot rhs

chcLhs :: Chc v -> [App v]
chcLhs (Rule lhs _ _) = lhs
chcLhs (Query lhs _ _) = lhs

chcBindings :: Chc v -> [v]
chcBindings (Rule _ _ rhs) = appOperands rhs
chcBindings Query{} = []

predicates :: Chc v -> [v]
predicates (Rule lhs _ rhs) = map appOperator (lhs ++ [rhs])
predicates (Query lhs _ _) = map appOperator lhs

applyChc :: Eq v => (App v -> Form v) -> Chc v -> Form v
applyChc f = \case
  Query lhs ctx rhs -> app2 Impl (manyAnd (ctx : map f lhs)) rhs
  Rule  lhs ctx rhs -> app2 Impl (manyAnd (ctx : map f lhs)) (f rhs)

isQuery :: Chc v -> Bool
isQuery Query{} = True
isQuery _ = False

instance Pretty v => Pretty (Chc v) where
  pretty (Rule as f h)  = sep (map pretty as ++ [pretty f, pretty "=>", pretty h])
  pretty (Query as f h) = sep (map pretty as ++ [pretty f, pretty "=>", pretty h])

instance Pretty v => Pretty (App v) where
  pretty a = braces (sep
    (pretty (appOperator a) : map pretty (appOperands a)))
