{-# LANGUAGE QuasiQuotes #-}
import           Data.Text.Prettyprint.Doc
import qualified Data.Map as M
import           Data.Loc
import           Data.Functor.Identity
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Graph.Extras as G

import           Language.Structured
import           Logic.Formula as F
import           Logic.ImplicationGraph
import           Logic.Solver.Equivalence

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
  [ (Call "f-mul" [[form|fx|], [form|fy + fz|]] [fr], [fx, fy, fz, fr])
  ]

fa, fb, fmt, fm :: Var
fa  = Var ["fa"] 0 False F.Int
fb  = Var ["fb"] 0 False F.Int
fmt = Var ["fmt"] 0 False F.Int
fm  = Var ["fm"] 0 False F.Int

fmul :: Imp
fmul =
  [ (Br [form|fb = 0|]
    [ (fm := [form|0|]                              , [fm, fa, fb]) ]
    [ (Call "f-mul" [[form|fa|], [form|fb-1|]] [fmt], [fm, fa, fb, fmt])
    , (fm := [form|fmt + fa|]                       , [fm, fa, fb, fmt])
    ]                                               , [fm, fa, fb])
  ]


gg :: Graph Loc (Identity Form) Inst
gg = impGraph g

g :: Program
g =
  Program
  { _entryPoint = "g"
  , _procedures = M.fromList
    [ ("g", ([], [], gbody))
    , ("g-mul", ([ga, gb], [gm], gmul))
    ]
  }

gx, gy, gz, gt, gr :: Var
gx = Var ["gx"] 0 False F.Int
gy = Var ["gy"] 0 False F.Int
gz = Var ["gz"] 0 False F.Int
gt = Var ["gt"] 0 False F.Int
gs = Var ["gs"] 0 False F.Int
gr = Var ["gr"] 0 False F.Int

gbody :: Imp
gbody =
  [ (Call "g-mul" [[form|gx|], [form|gy|]] [gt], [gx, gy, gz, gt])
  , (Call "g-mul" [[form|gx|], [form|gz|]] [gs], [gx, gy, gz, gt, gs])
  , (gr := [form|gt + gs|], [gx, gy, gz, gr])
  ]

ga, gb, gmt, gm :: Var
ga  = Var ["ga"] 0 False F.Int
gb  = Var ["gb"] 0 False F.Int
gmt = Var ["gmt"] 0 False F.Int
gm  = Var ["gm"] 0 False F.Int

gmul :: Imp
gmul =
  [ (Br [form|gb = 0|]
    [ (gm := [form|0|]                              , [gm, ga, gb]) ]
    [ (Call "g-mul" [[form|ga|], [form|gb-1|]] [gmt], [gm, ga, gb, gmt])
    , (gm := [form|gmt + ga|]                       , [gm, ga, gb, gmt])
    ]                                               , [gm, ga, gb])
  ]

example :: IO ()
example = do
  G.display "f" fg
  G.display "g" gg
  sol <- solve [form|fx = gx
                  && fy = gy
                  && fz = gz
                  && fx >= 0
                  && fy >= 0
                  && fz <= 0
                  -> fr = gr|] fg gg
  case sol of
    Left e -> print (pretty e)
    Right sol' ->
      G.display "sol" sol'
