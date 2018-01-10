{-# LANGUAGE TemplateHaskell #-}
module Formula.Type where

import           Control.Lens hiding (List)
import           Data.Data (Data)
import           Data.Text.Prettyprint.Doc

data Type
  = Unit
  | Bool
  | Int
  | Real
  | Type :=> Type
  | List Type
  | Array Type Type
  deriving (Show, Read, Eq, Ord, Data)

infixr 0 :=>

makePrisms ''Type

instance Pretty Type where
  pretty = \case
    Unit        -> pretty "Unit"
    Bool        -> pretty "Bool"
    Int         -> pretty "Int"
    Real        -> pretty "Real"
    t :=> t'    -> pretty t <+> pretty "->" <+> pretty t'
    List t      -> pretty "List<" <> pretty t <> pretty ">"
    Array t1 t2 -> pretty "Array<" <> pretty t1 <> pretty "," <> pretty t2

-- | Construct a function type from a list of input types and an output type.
curryType :: [Type] -> Type -> Type
curryType [] ran = ran
curryType dom ran = foldr (:=>) ran dom

-- | The argument types of some type.
domain :: Type -> [Type]
domain (t :=> t') = t : domain t'
domain _ = []

-- | The resultant type when the type is fully applied.
range :: Type -> Type
range (_ :=> t) = range t
range t = t
