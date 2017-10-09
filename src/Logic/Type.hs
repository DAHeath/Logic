module Logic.Type where

import           Data.Data (Data)
import           Text.PrettyPrint.HughesPJClass

data Type
  = Unit
  | Bool
  | Int
  | Real
  | Type :=> Type
  | List Type
  deriving (Show, Read, Eq, Ord, Data)

infixr 0 :=>

instance Pretty Type where
  pPrint = \case
    Unit     -> text "Unit"
    Bool     -> text "Bool"
    Int      -> text "Int"
    Real     -> text "Real"
    t :=> t' -> pPrint t <+> text "->" <+> pPrint t'
    List t   -> text "List<" <> pPrint t <> text ">"

class Typed a where
  typeOf :: a -> Type

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
