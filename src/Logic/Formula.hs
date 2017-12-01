{-# LANGUAGE TemplateHaskell, DeriveFunctor, DeriveTraversable #-}
module Logic.Formula where

import           Control.Lens

import           Data.Data (Data)
import           Data.Data.Lens (uniplate)
import           Data.Text.Prettyprint.Doc

import           Logic.Type (Type((:=>)), Typed)
import qualified Logic.Type as T

data Form v
  = Form v :@ Form v
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

  | Store Type Type
  | Select Type Type

  | LUnit
  | LBool Bool
  | LInt Integer
  | LReal Double
  deriving (Show, Read, Eq, Ord, Data, Functor, Foldable, Traversable)

infixl 9 :@

makePrisms ''Form

instance Data v => Plated (Form v) where plate = uniplate

instance Eq v => Monoid (Form v) where
  mappend = mkAnd
  mempty = LBool True

instance Typed v => Typed (Form v) where
  typeOf = \case
    V v         -> T.typeOf v
    v :@ _      -> case T.typeOf v of
                     _ :=> t -> t
                     _ -> error "bad function application type"

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

    Select t t' -> T.Array t t' :=> t :=> t' :=> T.Array t t'
    Store t t'  -> T.Array t t' :=> t :=> t'

    LUnit       -> T.Unit
    LBool _     -> T.Bool
    LInt _      -> T.Int
    LReal _     -> T.Real

instance Pretty v => Pretty (Form v) where
  pretty = \case
    f :@ x :@ y ->
      if isBinaryInfix f
      then hsep [binArg x, pretty f, binArg y]
      else parens (inlinePrint f x <+> pretty y)
    V v          -> pretty v
    f :@ x       -> parens (pretty f <+> pretty x)

    If _         -> pretty "if"

    Distinct _   -> pretty "distinct"

    And          -> pretty "&&"
    Or           -> pretty "||"
    Impl         -> pretty "->"
    Iff          -> pretty "<->"
    Not          -> pretty "not"

    Add _        -> pretty "+"
    Mul _        -> pretty "*"
    Sub _        -> pretty "-"
    Div _        -> pretty "/"
    Mod _        -> pretty "%"

    Eql _        -> pretty "="
    Lt _         -> pretty "<"
    Le _         -> pretty "<="
    Gt _         -> pretty ">"
    Ge _         -> pretty ">="

    Store{}      -> pretty "store"
    Select{}     -> pretty "select"

    LUnit        -> pretty "()"
    LBool b      -> pretty b
    LInt i       -> pretty i
    LReal r      -> pretty r
    where
      binArg f = if isLit f || isVar f then pretty f else parens (pretty f)

      inlinePrint f x = case f of
        f' :@ y -> inlinePrint f' y <+> pretty x
        f' -> pretty f' <+> pretty x

class Formulaic a where
  toForm :: Eq v => a v -> Form v

instance Formulaic Form where
  toForm = id

-- | Apply a function to two arguments.
app2 :: Form v -> Form v -> Form v -> Form v
app2 f x y = f :@ x :@ y

app3 :: Form v -> Form v -> Form v -> Form v -> Form v
app3 f x y z = f :@ x :@ y :@ z

appMany :: Form v -> [Form v] -> Form v
appMany = foldl (:@)

mkAnd :: Eq v => Form v -> Form v -> Form v
mkAnd x@(Ge t1 :@ x1 :@ y1) y@(Le t2 :@ x2 :@ y2)
  | t1 == t2 && x1 == x2 && y1 == y2 = Eql t1 :@ x1 :@ y1
  | otherwise                        = app2 And x y
mkAnd x@(Le t1 :@ x1 :@ y1) y@(Ge t2 :@ x2 :@ y2)
  | t1 == t2 && x1 == x2 && y1 == y2 = Eql t1 :@ x1 :@ y1
  | otherwise                        = app2 And x y
mkAnd x@(Le t1 :@ x1 :@ y1) y@(Le t2 :@ y2 :@ x2)
  | t1 == t2 && x1 == x2 && y1 == y2 = Eql t1 :@ x1 :@ y1
  | otherwise                        = app2 And x y
mkAnd x@(Ge t1 :@ x1 :@ y1) y@(Ge t2 :@ y2 :@ x2)
  | t1 == t2 && x1 == x2 && y1 == y2 = Eql t1 :@ x1 :@ y1
  | otherwise                        = app2 And x y
mkAnd x y
  | x == LBool False = LBool False
  | y == LBool False = LBool False
  | x == LBool True  = y
  | y == LBool True  = x
  | x == y           = x
  | otherwise        = app2 And x y

mkOr :: Eq v => Form v -> Form v -> Form v
mkOr x y
  | x == LBool True  = LBool True
  | y == LBool True  = LBool True
  | x == LBool False = y
  | y == LBool False = x
  | x == y           = x
  | otherwise        = app2 Or x y

mkNot :: Form v -> Form v
mkNot (Not :@ y) = y
mkNot x = Not :@ x

mkEql :: Eq v => Type -> Form v -> Form v -> Form v
mkEql t x y
  | x == y = LBool True
  | otherwise = app2 (Eql t) x y

manyAnd, manyOr :: (Foldable f, Eq v) => f (Form v) -> Form v
manyAnd = foldr mkAnd (LBool True)
manyOr  = foldr mkOr (LBool False)

mkIAdd :: Form v -> Form v -> Form v
mkIAdd (LInt 0) x = x
mkIAdd x (LInt 0) = x
mkIAdd (LInt x) (LInt y) = LInt (x + y)
mkIAdd x y = Add T.Int :@ x :@ y

mkIMul :: Form v -> Form v -> Form v
mkIMul (LInt 0) _ = LInt 0
mkIMul _ (LInt 0) = LInt 0
mkIMul (LInt 1) x = x
mkIMul x (LInt 1) = x
mkIMul (LInt x) (LInt y) = LInt (x * y)
mkIMul x y = Mul T.Int :@ x :@ y

manyIAdd, manyIMul :: Foldable f => f (Form v) -> Form v
manyIAdd = foldr mkIAdd (LInt 0)
manyIMul = foldr mkIMul (LInt 1)

-- | Is the formula a literal?
isLit :: Form v -> Bool
isLit = \case
  LUnit   -> True
  LBool _ -> True
  LInt _  -> True
  LReal _ -> True
  _       -> False

-- | Is the formula simply a variable?
isVar :: Form v -> Bool
isVar = \case
  V _ -> True
  _   -> False

-- | Is the formula an infix operator?
isBinaryInfix :: Form v -> Bool
isBinaryInfix = \case
    And   -> True
    Or    -> True
    Impl  -> True
    Iff   -> True
    Add _ -> True
    Mul _ -> True
    Sub _ -> True
    Div _ -> True
    Mod _ -> True
    Eql _ -> True
    Lt _  -> True
    Le _  -> True
    Gt _  -> True
    Ge _  -> True
    _     -> False

-- | Map vars to something else
mapVar :: (v -> v) -> Form v -> Form v
mapVar f = \case
    V var -> V $ f var
    left :@ right -> mapVar f left :@ mapVar f right
    other -> other
