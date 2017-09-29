{-# LANGUAGE DeriveDataTypeable, LambdaCase #-}
module Logic.Chc where

import           Logic.Formula
import           Logic.Model

import           Control.Lens

import           Data.Data (Data)
import           Data.Monoid ((<>))
import qualified Data.Map as M
import qualified Data.Set as S

import           Text.PrettyPrint.HughesPJClass (Pretty, pPrint)
import qualified Text.PrettyPrint.HughesPJClass as PP

data Chc
  = Rule [App] Form App
  | Query [App] Form Form
  deriving (Show, Eq, Ord, Data)

instance Variadic Chc where
  vars = \case
    Rule as f a -> S.unions (map vars as ++ [vars f, vars a])
    Query as f q -> S.unions (map vars as ++ [vars f, vars q])
  subst m = \case
    Rule as f a -> Rule (map (subst m) as) (subst m f) (subst m a)
    Query as f q -> Query (map (subst m) as) (subst m f) (subst m q)

data App = App { appOperator :: Var, appOperands :: [Var] }
  deriving (Show, Eq, Ord, Data)

instance Variadic App where
  vars (App _ as) = S.fromList as
  subst m (App f as) = App f (map search as)
    where
      search v = M.findWithDefault v v m

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

chcBindings :: Chc -> [Var]
chcBindings (Rule _ _ rhs) = appOperands rhs
chcBindings Query{} = []

chcApp :: Chc -> Maybe App
chcApp (Rule _ _ rhs) = Just rhs
chcApp Query{} = Nothing

predicates :: Chc -> [Var]
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

isQuery :: Chc -> Bool
isQuery Query{} = True
isQuery _ = False

instance Pretty Chc where
  pPrint (Rule as f h)  = PP.sep (map pPrint as ++ [pPrint f, PP.text "=>", pPrint h])
  pPrint (Query as f h) = PP.sep (map pPrint as ++ [pPrint f, PP.text "=>", pPrint h])

instance Pretty App where
  pPrint a = PP.braces (PP.sep
    (PP.text (varName (appOperator a)) : map pPrint (appOperands a)))

substituteApps :: (App -> Form) -> Chc -> Form
substituteApps f = \case
  Rule  as b h -> app2 Impl (mkAnd (b : map f as)) (f h)
  Query as b h -> app2 Impl (mkAnd (b : map f as)) h

applyModelToApp :: Model -> App -> Form
applyModelToApp (Model m) (App fun vs) =
  instantiate vs ((\f -> M.findWithDefault (LBool False) f m) fun)
