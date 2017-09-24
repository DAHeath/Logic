{-# LANGUAGE LambdaCase
           , DeriveDataTypeable
           , DeriveFunctor
           , DeriveTraversable
           , FlexibleContexts
           , FlexibleInstances
           , OverloadedStrings
           , PatternSynonyms
           , TemplateHaskell
           , StandaloneDeriving
           #-}

module Logic.Formula where

import           Logic.Type (Type((:=>)), Typed)
import qualified Logic.Type as T

import           Bound

import           Control.Lens

import           Data.Data (Data)
import           Data.Data.Lens (uniplate)
import           Data.Monoid ((<>))
import           Data.Eq.Deriving
import           Data.Ord.Deriving
import           Text.Show.Deriving

import           Text.PrettyPrint.HughesPJClass ((<+>), Pretty, pPrint)
import qualified Text.PrettyPrint.HughesPJClass as PP

type Name = String
data Variable = Variable { varType :: Type, varName :: Name }
  deriving (Show, Eq, Ord, Data)

instance Typed Variable
  where typeOf (Variable t _) = t

instance Pretty Variable
  where pPrint (Variable t n) = PP.text (n ++ ":") <> PP.pPrint t

data Form' v
  = Forall Type (Scope () Form' v)
  | Exists Type (Scope () Form' v)
  | Apply (Form' v) (Form' v)
  | V v

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
  deriving (Functor, Foldable, Traversable)

makeBound ''Form'

deriveEq1 ''Form'
deriveOrd1 ''Form'
deriveShow1 ''Form'
deriving instance Eq v => Eq (Form' v)
deriving instance Ord v => Ord (Form' v)
deriving instance Show v => Show (Form' v)
deriving instance Data v => Data (Form' v)

type Form = Form' Variable

test :: Form' Variable
test = manyForall [Variable T.Int "x", Variable T.Int "y"]
      (Apply (Apply (Eql T.Int) (V $ Variable T.Int "x"))
                                (V $ Variable T.Int "y"))

app2 :: Form' v -> Form' v -> Form' v -> Form' v
app2 f x y = Apply (Apply f x) y

appMany :: Form' v -> [Form' v] -> Form' v
appMany f xs = foldl Apply f xs

mkForall, mkExists :: (Typed v, Eq v) => v -> Form' v -> Form' v
mkForall v f = Forall (T.typeOf v) (abstract1 v f)
mkExists v f = Exists (T.typeOf v) (abstract1 v f)

manyForall, manyExists :: (Typed v, Eq v) => [v] -> Form' v -> Form' v
manyForall vs f = foldl (flip mkForall) f vs
manyExists vs f = foldl (flip mkExists) f vs

mkAnd, mkOr :: Foldable f => f (Form' v) -> (Form' v)
mkAnd = foldr (app2 And) (LBool True)
mkOr  = foldr (app2 Or) (LBool False)

instance Monoid (Form' v) where
  mappend = app2 And
  mempty = LBool True

instance Typed v => Typed (Form' v) where
  typeOf = \case
    Forall{}    -> T.Bool
    Exists{}    -> T.Bool
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

class PRec a where
  recPrint :: Int -> a -> PP.Doc

instance PRec Variable where
  recPrint = const pPrint

instance (PRec v, Pretty v) => PRec (Var () (Form' v)) where
  recPrint n (B ()) = PP.pPrint n
  recPrint n (F (V v)) = recPrint (n+1) v
  recPrint _ (F v) = PP.pPrint v

instance (PRec v, Pretty v) => Pretty (Var () (Form' v)) where
  pPrint = recPrint 0

instance (PRec v, Pretty v) => Pretty (Form' v) where
  pPrint = \case
    Forall t f   -> PP.text "forall" <+> PP.pPrint t <+> PP.parens (pPrint $ unscope f)
    Exists t f   -> PP.text "exists" <+> PP.pPrint t <+> PP.parens (pPrint $ unscope f)
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

instance Data v => Plated (Form' v) where
  plate = uniplate
