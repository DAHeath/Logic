{-# LANGUAGE DeriveDataTypeable, LambdaCase #-}
module Logic.Type where

import           Data.Data (Data)
import           Data.Monoid ((<>))

import           Text.PrettyPrint.HughesPJClass (Pretty, (<+>), pPrint)
import qualified Text.PrettyPrint.HughesPJClass as PP

data Type
  = Unit
  | Bool
  | Int
  | Real
  | Type :=> Type
  | List Type
  deriving (Show, Read, Eq, Ord, Data)

infixr 0 :=>

curryType :: [Type] -> Type -> Type
curryType [] ran = ran
curryType dom ran = foldr (:=>) ran dom

domain :: Type -> [Type]
domain (t :=> t') = t : domain t'
domain _ = []

range :: Type -> Type
range (_ :=> t) = range t
range t = t

instance Pretty Type where
  pPrint = \case
    Unit     -> PP.text "Unit"
    Bool     -> PP.text "Bool"
    Int      -> PP.text "Int"
    Real     -> PP.text "Real"
    t :=> t' -> pPrint t <+> PP.text "->" <+> pPrint t'
    List t   -> PP.text "List<" <> PP.pPrint t <> PP.text ">"

class Typed a where
  typeOf :: a -> Type
