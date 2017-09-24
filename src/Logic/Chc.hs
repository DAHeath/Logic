{-# LANGUAGE DeriveDataTypeable, LambdaCase #-}
module Logic.Chc where

import           Logic.Formula

import           Control.Lens

import           Data.Data (Data)
import           Data.Monoid ((<>))

import           Text.PrettyPrint.HughesPJClass (Pretty, pPrint)
import qualified Text.PrettyPrint.HughesPJClass as PP

data Chc
  = Rule [App] Form App
  | Query [App] Form Form
  deriving (Show, Eq, Ord, Data)

data App = App { appOperator :: Variable, appOperands :: [Variable] }
  deriving (Show, Eq, Ord, Data)

chcBody :: Lens' Chc Form
chcBody = lens getter setter
  where
    getter (Rule  _ f _) = f
    getter (Query _ f _) = f
    setter (Rule  lhs _ rhs) f = Rule lhs f rhs
    setter (Query lhs _ rhs) f = Query lhs f rhs

chcContext :: Chc -> Form
chcContext (Rule _ ctx _) = ctx
chcContext (Query _ ctx rhs) = ctx <> Apply Not rhs

chcLhs :: Chc -> [App]
chcLhs (Rule lhs _ _) = lhs
chcLhs (Query lhs _ _) = lhs

chcBindings :: Chc -> [Variable]
chcBindings (Rule _ _ rhs) = appOperands rhs
chcBindings Query{} = []

chcApp :: Chc -> Maybe App
chcApp (Rule _ _ rhs) = Just rhs
chcApp Query{} = Nothing

predicates :: Chc -> [Variable]
predicates (Rule lhs _ rhs) = map appOperator (lhs ++ [rhs])
predicates (Query lhs _ _) = map appOperator lhs

appToForm :: App -> Form
appToForm (App rel vs) = appMany (V rel) (map V vs)

chcToForm :: Chc -> Form
chcToForm (Rule lhs phi rhs) = app2 Impl (mkAnd (map appToForm lhs ++ [phi])) (appToForm rhs)
chcToForm (Query lhs phi goal) = app2 Impl (mkAnd (map appToForm lhs ++ [phi])) goal

applyChc :: (App -> Form) -> Chc -> Form
applyChc f = \case
  Query lhs ctx rhs -> app2 Impl (mkAnd (ctx : map f lhs)) rhs
  Rule  lhs ctx rhs -> app2 Impl (mkAnd (ctx : map f lhs)) (f rhs)

-- applyModelToApp :: Model -> App -> Form
-- applyModelToApp (Model m) (App fun vs) =
--   instantiate vs ((\f -> M.findWithDefault (LBool False) f m) fun)

isQuery :: Chc -> Bool
isQuery Query{} = True
isQuery _ = False

-- instance Variadic App where
--   variables = S.fromList . appOperands
--   substitute m (App f vs) = App f (substitute m vs)

-- instance Variadic Chc where
--   variables (Rule  lhs f rhs) = variables lhs <> variables f <> variables rhs
--   variables (Query lhs f rhs) = variables lhs <> variables f <> variables rhs

--   substitute m (Rule  lhs f rhs) = Rule  (substitute m lhs) (substitute m f) (substitute m rhs)
--   substitute m (Query lhs f rhs) = Query (substitute m lhs) (substitute m f) (substitute m rhs)

instance Pretty Chc where
  pPrint (Rule as f h)  = PP.sep (map pPrint as ++ [pPrint f, PP.text "=>", pPrint h])
  pPrint (Query as f h) = PP.sep (map pPrint as ++ [pPrint f, PP.text "=>", pPrint h])

instance Pretty App where
  pPrint a = PP.braces (PP.sep
    (PP.text (varName (appOperator a)) : map pPrint (appOperands a)))
