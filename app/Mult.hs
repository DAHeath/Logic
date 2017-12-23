{-# LANGUAGE QuasiQuotes #-}
import qualified Data.Map as M
import           Data.Loc
import           Data.Functor.Identity
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Graph.Extras as G

import           Language.Structured
import qualified Language.Unstructured as U
import           Logic.Formula as F
import           Logic.ImplicationGraph

fg :: Graph Loc (Identity Form) Inst
fg = impGraph f

f :: Program
f =
  Program
  { _entryPoint = "f"
  , _procedures = M.fromList
    [ ("f", ([], [], fbody))
    , ("f-mul", ([fa, fb], [fm], fmul))
    ]
  }

fx, fy, fz, ft, fr :: Var
fx = Var ["fx"] 0 False F.Int
fy = Var ["fy"] 0 False F.Int
fz = Var ["fz"] 0 False F.Int
ft = Var ["ft"] 0 False F.Int
fr = Var ["fr"] 0 False F.Int

fbody :: Imp
fbody =
  [ (Call "f-mul" [[form|fx|], [form|fy|]] [ft], [fx, fy, fz, ft])
  , (Call "f-mul" [[form|ft|], [form|fz|]] [fr], [fz])
  ]

fa, fb, fmt, fm :: Var
fa  = Var ["fa"] 0 False F.Int
fb  = Var ["fb"] 0 False F.Int
fmt = Var ["fmt"] 0 False F.Int
fm  = Var ["fm"] 0 False F.Int

fmul :: Imp
fmul =
  [ (Br [form|fa = 0|]
    [ (fm := [form|0|]                              , [fm, fa, fb]) ]
    [ (Call "f-mul" [[form|fa|], [form|fb-1|]] [fmt], [fm, fa, fb, fmt])
    , (fm := [form|fmt + fa|]                       , [fm, fa, fb, fmt])
    ]                                               , [fm, fa, fb])
  ]

-- mult :: Graph Loc (Identity Form) Inst
-- mult = singleProc "
