{-# LANGUAGE QuasiQuotes #-}
module Language.Imp where

import           Control.Lens
import           Control.Arrow (second)

import           Data.Data (Data)
import qualified Data.Set as S
import qualified Data.Optic.Directed.HyperGraph as G
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Graph.Extras as G

import           Logic.Formula.Parser
import qualified Logic.Type as T
import           Logic.Formula
import           Logic.Var
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Simplify
import           Logic.ImplicationGraph.LTree
import           Logic.ImplicationGraph.Safety

data Com
  = Var := Form
  | Jump Integer
  | Cond Form Integer
  | Done
  deriving (Show, Read, Eq, Ord, Data)

type Imp = [(Com, [Var])]

impGraph :: Form -> Imp -> Graph Loc Edge Inst
impGraph q cs = G.fromLists verts edges & ix (Loc end) . instForm .~ (q & vars %~ setLoc end)
  where
    end = toInteger $ length cs - 1
    verts = tail $
      zipWith vertOf [0..] (map snd cs) ++ [(Loc end, Inst (Loc end) [] (LBool True))]
    edges = map (second Leaf) $ concat $ zipWith edgesOf [0..] cs

    vertOf l vs = (Loc l, emptyInst (Loc l) (map (setLoc l) vs))

    edgesOf l (c, vs) = case c of
      v := f ->
        let f' = (f & vars %~ setLoc l)
            vs' = filter (/= v) vs
        in
        [ edgeFrom l (l+1)
          $ mkAnd
              (mkEql (T.typeOf v) (V $ setNew $ setLoc (l+1) v) f')
              (varCarry l (l+1) vs')
        ]
      Jump l' ->
        [ edgeFrom l l' $ varCarry l l' vs ]
      Cond f l' ->
        [ edgeFrom l l' 
          $ mkAnd
              (f & vars %~ setLoc l)
              (varCarry l l' vs)
        , edgeFrom l (l+1)
          $ mkAnd
              (mkNot f & vars %~ setLoc l)
              (varCarry l (l+1) vs)
        ]
      Done -> []
    setLoc l v = v & _Free . _1 . freeVLoc .~ l
    setNew v = v & _Free . _1 . freeVNew .~ True
    edgeFrom l l' e =
      if l == 0
      then (G.HEdge S.empty (Loc l'), e)
      else (G.HEdge (S.singleton (Loc l)) (Loc l'), e)

    varCarry l l' vs =
      let bef = vs & map (setLoc l)
          aft = vs & map (setLoc l') & map setNew
      in
      manyAnd $ zipWith (\v1 v2 -> mkEql (T.typeOf v1) (V v1) (V v2)) bef aft


x = Free (FreeV ["x"] 0 False) T.Int
n = Free (FreeV ["n"] 0 False) T.Int

prog :: Imp
prog =
  [ (x := [form|0|], [])                    -- 0
  , (Cond [form|x:Int >= n:Int|] 4, [x, n]) -- 1
  , (x := [form|x:Int + 2|], [x, n])        -- 2
  , (Jump 1, [x, n])                        -- 3
  , (Done, [x,n])                           -- 4
  ]

test = impGraph [form|not (x:Int = 7)|] prog
