{-# LANGUAGE QuasiQuotes #-}
import           Control.Lens
import           Control.Monad.State

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Data (Data)
import           Data.Text.Prettyprint.Doc
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Graph.Extras as G

import           Logic.Formula.Parser
import           Logic.Formula hiding (If)
import           Logic.Var
import qualified Logic.Type as T
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Simplify
import           Logic.ImplicationGraph.Safety

import qualified Language.Unstructured as U

data Com
  = Var := Form
  | If Form Imp Imp
  | While Form Imp
  | Call ProcName [Form] [Var]
  deriving (Show, Read, Eq, Ord, Data)

type ProcName = String

type Imp = [(Com, [Var])]

data Program =
  Program
  { _entryPoint :: ProcName
  , _procedures :: Map ProcName ([Var], [Var], Imp)
  } deriving (Show, Read, Eq, Ord, Data)

impGraph :: Form -> Program -> Graph Loc Edge Inst
impGraph f = U.impGraph f . compile

compile :: Program -> U.Program
compile (Program ep ps) =
  U.Program ep (ps & traverse . _3 %~ proc)

proc :: Imp -> U.Imp
proc cs = concat (evalState (mapM comp cs) 0) ++ [(U.Done, vs')]
  where
    vs' = snd (last cs)

    comp :: (Com, [Var]) -> State Integer U.Imp
    comp (c, vs) = case c of
      v := f -> do
        _ <- inc
        return [(v U.:= f, vs)]
      If c cs1 cs2 -> do
        _ <- inc
        cs2' <- compM cs2
        l1 <- inc
        cs1' <- compM cs1
        l2 <- get
        return (((U.Cond c l1, vs) : cs2') ++ ((U.Jump l2, vs) : cs1'))
      While c cs -> do
        s <- get
        _ <- inc
        cs' <- compM cs
        e <- inc
        return ((U.Cond (mkNot c) e, vs) : cs' ++ [(U.Jump s, vs)])
      Call pn args ret -> do
        _ <- inc
        return [(U.Call pn args ret, vs)]

    compM = fmap concat . mapM comp
    inc = modify (+1) >> get

x = Free (FreeV ["x"] 0 False) T.Int
n = Free (FreeV ["n"] 0 False) T.Int
r = Free (FreeV ["r"] 0 False) T.Int

prog1 :: Imp
prog1 =
  [
    (If [form|x:Int >= n:Int|]
      [ (x := [form|x:Int + 1|], [x,n]) ]
      [ (x := [form|x:Int + 2|], [x,n]) ]
        , [x, n])
  ]

prog2 :: Imp
prog2 =
  [
    (x := [form|0|], [])
    , (While [form|x:Int < n:Int|]
        [ (x := [form|x:Int + 2|], [x,n]) ]
      , [x,n])

  ]

f :: Program
f = Program
  { _entryPoint = "f"
  , _procedures =
      M.singleton "f" ([n, x], [r],
        [ ( If [form|n:Int <= 0|]
               [ (r := [form|x:Int|], [r,n,x]) ]
               [ (Call "f" [[form|n:Int - 1|], [form|x:Int + n:Int|]] [r], [r,n,x]) ]
          , [r,n,x]) ])
  }

loop :: Program
loop = Program
  { _entryPoint = "loop"
  , _procedures =
    M.singleton "loop" ([], [],
      [ ( x := [form|0|], [x, n] )
      , ( While [form|x:Int < n:Int|]
          [ (x := [form|x:Int + 2|], [x, n])
          ], [x,n])
      ])
  }

-- prog :: Imp
-- prog =
--   [ (x := [form|0|], [])                    -- 0
--   , (Cond [form|x:Int >= n:Int|] 4, [x, n]) -- 1
--   , (x := [form|x:Int + 2|], [x, n])        -- 2
--   , (Jump 1, [x, n])                        -- 3
--   , (Done, [x,n])                           -- 4
--   ]

-- test = impGraph [form|not (x:Int = 7)|] prog
