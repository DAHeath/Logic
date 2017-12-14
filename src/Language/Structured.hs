module Language.Structured where

import           Control.Lens
import           Control.Monad.State

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Data (Data)
import           Data.Loc
import           Data.Optic.Directed.HyperGraph (Graph)

import           Logic.Formula
import           Logic.ImplicationGraph.Types

import qualified Language.Unstructured as U

-- | A simple structured, imperative language which can be used to construct
-- examples and which serves as a reference implementation.

-- | Structured programs have assignments, branches (if statements),
-- while loops, and procedure calls.
data Com
  -- Assign the variable to the result of the formula.
  = Var := Form
  -- If the condition holds, perform the first list of instructions. Otherwise,
  -- perform the second list of instructions.
  | Br Form Imp Imp
  -- Repeat the inner instructures until the condition does not hold
  | While Form Imp
  -- Call a procedure by name with the given arguments, putting the resulting
  -- values into the given variables.
  | Call ProcName [Form] [Var]
  deriving (Show, Read, Eq, Ord, Data)

-- | An imperative instruction is a command paired with the variables which are
-- live at the instruction.
type Imp = [(Com, [Var])]

type ProcName = String

-- | A program is a map of procedures, where the procedures are indexed by
-- their name. There is also a distinuished procedure name which is the entry
-- point of the program.
data Program =
  Program
  { _entryPoint :: ProcName
  , _procedures :: Map ProcName ([Var], [Var], Imp)
  } deriving (Show, Read, Eq, Ord, Data)

-- | Create a program graph consisting of one procedure which is allowed to
-- call itself.
singleProc :: Edge f => ProcName -> [Var] -> [Var] -> Imp -> Graph Loc (f Form) Inst
singleProc pn inp out instrs = impGraph Program
  { _entryPoint = pn
  , _procedures = M.singleton pn (inp, out, instrs)
  }

-- | Create a program graph consisting of one procedure with no recursion.
singleNonRec :: Edge f => Imp -> Graph Loc (f Form) Inst
singleNonRec = singleProc "" [] []

-- | Create a program graph.
impGraph :: Edge f => Program -> Graph Loc (f Form) Inst
impGraph = U.impGraph . compile

-- | Convert a structured program into an unstructured program.
compile :: Program -> U.Program
compile (Program ep ps) = U.Program ep (ps & traverse . _3 %~ proc)

-- | Convert a list of structured instructions to a list of unstructured
-- instructions.
proc :: Imp -> U.Imp
proc cs = concat (evalState (mapM comp cs) 0) ++ [(U.Done, vs')]
  where
    vs' = snd (last cs)

    comp :: (Com, [Var]) -> State Integer U.Imp
    comp (c, vs) = case c of
      v := f -> do
        _ <- inc
        return [(v U.:= f, vs)]
      Br cond cs1 cs2 -> do
        _ <- inc
        cs2' <- compM cs2
        l1 <- inc
        cs1' <- compM cs1
        l2 <- get
        return (((U.Cond cond l1, vs) : cs2') ++ ((U.Jump l2, vs) : cs1'))
      While cond insts -> do
        s <- get
        _ <- inc
        cs' <- compM insts
        e <- inc
        return ((U.Cond (mkNot cond) e, vs) : cs' ++ [(U.Jump s, vs)])
      Call pn args ret -> do
        _ <- inc
        return [(U.Call pn args ret, vs)]

    compM = fmap concat . mapM comp
    inc = modify (+1) >> get
