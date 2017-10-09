module Logic.Chc where

import           Data.Data (Data)
import           Data.Monoid ((<>))
import qualified Data.Map as M

import           Logic.Formula
import           Logic.Model
import           Logic.Var

import           Text.PrettyPrint.HughesPJClass (Pretty, pPrint)
import qualified Text.PrettyPrint.HughesPJClass as PP

data Chc
  = Rule [App] Form App
  | Query [App] Form Form
  deriving (Show, Eq, Ord, Data)

data App = App { appOperator :: Var, appOperands :: [Var] }
  deriving (Show, Eq, Ord, Data)

instance Formulaic Chc where
  toForm (Rule lhs phi rhs) = app2 Impl (manyAnd (map toForm lhs ++ [phi])) (toForm rhs)
  toForm (Query lhs phi goal) = app2 Impl (manyAnd (map toForm lhs ++ [phi])) goal

instance Formulaic App where
  toForm (App rel vs) = appMany (V rel) (map V vs)

chcContext :: Chc -> Form
chcContext (Rule _ ctx _) = ctx
chcContext (Query _ ctx rhs) = ctx <> Apply Not rhs

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
  pPrint (Rule as f h)  = PP.sep (map pPrint as ++ [pPrint f, PP.text "=>", pPrint h])
  pPrint (Query as f h) = PP.sep (map pPrint as ++ [pPrint f, PP.text "=>", pPrint h])

instance Pretty App where
  pPrint a = PP.braces (PP.sep
    (PP.text (varName (appOperator a)) : map pPrint (appOperands a)))

applyModelToApp :: Model -> App -> Form
applyModelToApp (Model m) (App fun vs) =
  instantiate vs ((\f -> M.findWithDefault (LBool False) f m) fun)
