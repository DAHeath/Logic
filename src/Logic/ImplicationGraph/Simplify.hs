module Logic.ImplicationGraph.Simplify where

import qualified Data.Map as Map
import           Data.Maybe
import qualified Logic.Var as V
import           Logic.Formula
import           Logic.ImplicationGraph


cartesianProduct :: (a -> b -> c) -> [a] -> [b] -> [c]
cartesianProduct f as bs = [ f a b | a <- as, b <- bs ]


conjunction :: Edge -> Edge -> Edge
conjunction edge edge' =
  let
    bumpVarBy bumper var =
      V.bumpVar ((+) $ fromMaybe 0 $ Map.lookup (V.path var) bumper) var

    conflicts = Map.mapKeys V.path $
                Map.mapMaybe V.aliasCount $ _edgeMap edge
  in Edge {
    _edgeForm = mkAnd
                (_edgeForm edge)
                (mapVar (bumpVarBy conflicts) $ _edgeForm edge'),
    _edgeMap = Map.union
               (Map.map (bumpVarBy conflicts) $ _edgeMap edge')
               (_edgeMap edge)
    }


disjunction :: Edge -> Edge -> Edge
disjunction = undefined

