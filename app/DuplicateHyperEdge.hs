{-# LANGUAGE NoMonomorphismRestriction, QuasiQuotes #-}
import qualified Data.Optic.Directed.HyperGraph as G
import qualified Data.Optic.Graph.Extras as G
import qualified Data.Set as S
import Data.Loc
import Data.Functor.Identity

import Logic.ImplicationGraph
import Logic.Formula as F

x :: Var
x = Var ["x"] 0 False F.Int

test = G.fromLists
  [ (0, emptyInst (Loc 0) [x])
  , (1, emptyInst (Loc 1) [x])
  , (2, emptyInst (Loc 2) [x])
  , (3, emptyInst (Loc 3) [x])
  ]
  [ (G.HEdge S.empty 0, Identity $ LBool True)
  , (G.HEdge S.empty 1, Identity $ LBool True)
  , (G.HEdge (S.fromList [1]) 2, Identity [form|x/1 = x+1|])
  , (G.HEdge (S.fromList [0]) 2, Identity [form|x/1 = x+1|])
  , (G.HEdge (S.fromList [0, 2]) 3, Identity [form|x/2 = x/1+1|])
  , (G.HEdge (S.singleton 0) 0, Identity $ LBool True)
  ]
