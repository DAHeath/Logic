{-# LANGUAGE LambdaCase
           , DeriveDataTypeable
           , FlexibleContexts
           , FlexibleInstances
           , OverloadedStrings
           , PatternSynonyms
           #-}

module Logic.Formula where

import           Logic.Type (Type((:=>)), Typed)
import qualified Logic.Type as T
import           Logic.Var

import           Control.Lens

import           Data.Data (Data)
import           Data.Data.Lens (biplate, uniplate)
import           Data.Monoid ((<>))
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S

import           Text.PrettyPrint.HughesPJClass ((<+>), Pretty, pPrint)
import qualified Text.PrettyPrint.HughesPJClass as PP

data Form
  = Apply Form Form
  | V Var

  | If Type

  | Not
  | Impl
  | Iff
  | And
  | Or

  | Add Type
  | Mul Type
  | Sub Type
  | Div Type
  | Mod Type

  | Distinct Type
  | Eql Type
  | Lt  Type
  | Le  Type
  | Gt  Type
  | Ge  Type

  | LUnit
  | LBool Bool
  | LInt Integer
  | LReal Double
  deriving (Show, Read, Eq, Ord, Data)

instance Plated Form where
  plate = uniplate

instance Variadic Form where
  vars f = f ^.. biplate & S.fromList
  subst m = transform
    (\case V v -> V $ M.findWithDefault v v m
           f   -> f)

substForm :: Map Var Var -> Form -> Form
substForm m = transform
  (\case V v -> V $ M.findWithDefault v v m
         f   -> f)

formVars :: Form -> Set Var
formVars f = f ^.. biplate & S.fromList

app2 :: Form -> Form -> Form -> Form
app2 f x = Apply (Apply f x)

appMany :: Form -> [Form] -> Form
appMany = foldl Apply

mkAnd, mkOr :: Foldable f => f Form -> Form
mkAnd = foldr (app2 And) (LBool True)
mkOr  = foldr (app2 Or) (LBool False)

instance Monoid Form where
  mappend = app2 And
  mempty = LBool True

instance Typed Form where
  typeOf = \case
    V v         -> T.typeOf v
    Apply v _   -> case T.typeOf v of
                     _ :=> t -> t
                     _ -> undefined

    If t        -> T.Bool :=> t :=> t :=> t

    Not         -> T.Bool :=> T.Bool
    Impl        -> T.Bool :=> T.Bool
    Iff         -> T.Bool :=> T.Bool
    And         -> T.Bool :=> T.Bool
    Or          -> T.Bool :=> T.Bool

    Add t       -> t :=> t :=> t
    Mul t       -> t :=> t :=> t
    Sub t       -> t :=> t :=> t
    Div t       -> t :=> t :=> t
    Mod t       -> t :=> t :=> t

    Distinct t  -> T.List t :=> T.Bool
    Eql t       -> t :=> t :=> T.Bool
    Lt t        -> t :=> t :=> T.Bool
    Le t        -> t :=> t :=> T.Bool
    Gt t        -> t :=> t :=> T.Bool
    Ge t        -> t :=> t :=> T.Bool

    LUnit       -> T.Unit
    LBool _     -> T.Bool
    LInt _      -> T.Int
    LReal _     -> T.Real

instance Pretty Form where
  pPrint = \case
    V v          -> PP.pPrint v
    Apply (Apply f x) y -> PP.parens (inlinePrint f x <+> pPrint y)
    Apply f x    -> PP.parens (pPrint f <+> pPrint x)

    If t         -> PP.text "if_" <> pPrint t

    Distinct t   -> PP.text "distinct_" <> pPrint t

    And          -> PP.text "&&"
    Or           -> PP.text "||"
    Impl         -> PP.text "->"
    Iff          -> PP.text "<->"
    Not          -> PP.text "not"

    Add t        -> PP.text "+"  <> pPrint t
    Mul t        -> PP.text "*"  <> pPrint t
    Sub t        -> PP.text "-"  <> pPrint t
    Div t        -> PP.text "/"  <> pPrint t
    Mod t        -> PP.text "%"  <> pPrint t

    Eql t        -> PP.text "="  <> pPrint t
    Lt t         -> PP.text "<"  <> pPrint t
    Le t         -> PP.text "<=" <> pPrint t
    Gt t         -> PP.text ">"  <> pPrint t
    Ge t         -> PP.text ">=" <> pPrint t

    LUnit         -> PP.text "()"
    LBool b       -> pPrint b
    LInt i        -> PP.text "#" <> pPrint i
    LReal r       -> pPrint r
    where
      inlinePrint f x = case f of
        Apply f' y -> inlinePrint f' y <+> pPrint x
        f' -> pPrint f' <+> pPrint x
