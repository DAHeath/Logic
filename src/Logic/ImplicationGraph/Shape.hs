module Logic.ImplicationGraph.Shape where

import           Control.Lens

import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Foldable (toList)

import           Logic.ImplicationGraph
import           Logic.Var
import           Logic.Formula
import qualified Logic.Type as T

import Debug.Trace

shapeAugment :: Set Var -- store objects
             -> Set Var -- load objects
             -> Graph Idx Edge Inst -- instance graph
             -> Graph (Loc' Idx) Edge Inst
shapeAugment ss ls g =
  addBranches $ subs (g & G.mapIdx Loc)
  where
    dag = G.withoutBackEdges g

    sverts :: [Idx]
    sverts = map (tip.fst) $ filter (isLOnly.snd) (dag ^@.. G.iallEdges)
    tip (G.HEdge _ i) = i

    loads = filter (isROnly.snd) (dag ^@.. G.iallEdges)

    isROnly = \case
      ROnly _ -> True
      _ -> False
    isLOnly = \case
      LOnly _ -> True
      _ -> False

    branches, joins :: [(G.HEdge (Loc' Idx), Edge)]
    branches = do
      s1 <- sverts
      s2 <- sverts
      (G.HEdge is i, e) <- loads
      return (G.HEdge (S.union
                        (S.map (LocPair (Loc s1) . Loc) is)
                        (S.map (LocPair (Loc s2) . Loc) is))
                      (LocPair (Loc s2) (Loc i)), e)
    joins = do
      s1 <- sverts
      (G.HEdge is i, e) <- loads
      return (G.HEdge (S.map (LocPair (Loc s1) . Loc) is) (Loc i), e)


    addBranches :: Graph (Loc' Idx) Edge Inst
                -> Graph (Loc' Idx) Edge Inst
    addBranches g = foldr (uncurry G.addEdge) g (branches ++ joins)


    sub :: Idx -> Graph (Loc' Idx) Edge Inst
    sub i = G.reached i dag
          & G.mapIdx (LocPair (Loc i) . Loc)
          & G.mapVert (locInst i)

    subs :: Graph (Loc' Idx) Edge Inst -> Graph (Loc' Idx) Edge Inst
    subs g' =
      foldr (\loc g'' ->
        let vs = (g ^?! ix loc) ^. instVars in
        G.union g'' (sub loc)
        & G.addEdge (G.HEdge (S.singleton (Loc loc))
          (LocPair (Loc loc) (Loc loc)))
          (Leaf $ groupUp vs (map zeroVar vs))) g' sverts

    zeroVar :: Var -> Var
    zeroVar v = v & varLoc .~ 0

    locInst :: Idx -> Inst -> Inst
    locInst i ins = ins & instVars %~ (\vs -> map zeroVar vs ++ vs)

    groupUp as bs = manyAnd $ zipWith (\a b -> mkEql (T.typeOf a) (V a) (V b)) as bs
