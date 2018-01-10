{-# LANGUAGE TemplateHaskell #-}
module Language.Language where

import           Control.Lens

import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Text.Prettyprint.Doc

import           Formula

-- | An unstructured program contains no structured loops of if statements.
-- Instead it supports only jumps (conditional and unconditional) and procedure
-- calls as control flow elements.
data Com
  -- Set the variable to the value of the formula and proceed to the next instruction.
  = Var := Expr
  -- Jump to the specified instruction if the condition holds. Otherwise, proceed to
  -- the next instruction.
  | Cond Expr Int
  -- Call the named procedure with the given arguments, assigning the results to the
  -- given variables. Then, proceed to the next instruction.
  | Call ProcName [Expr] [Var]
  -- A special marker indicating the end of the procedure. Every procedure should
  -- have a `Done` marker as the last instruction.
  | Done
  deriving (Show, Read, Eq, Ord, Data)

instance Pretty Com where
  pretty = \case
    v := f        -> pretty v <+> pretty ":=" <+> pretty f
    Cond f i      -> pretty "cond" <+> pretty f <+> pretty i
    Call pn as rs -> pretty "call" <+> pretty pn <+> pretty as <+> pretty rs
    Done          -> pretty "done"

type ProcName = String

type Imp = [(Com, [Var])]

-- | A program is a map of procedures, where the procedures are indexed by
-- their name. There is also a distinuished procedure name which is the entry
-- point of the program.
data Program =
  Program
  { _entryPoint :: ProcName
  , _procedures :: Map ProcName ([Var], [Var], Imp)
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Program

instance Pretty Program where
  pretty (Program ep ps) =
    pretty ep <+> pretty (M.toList ps)
