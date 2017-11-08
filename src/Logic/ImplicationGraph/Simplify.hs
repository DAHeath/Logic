module Logic.ImplicationGraph.Simplify where

import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.Maybe
import qualified Logic.Var as V
import           Logic.Formula
import           Logic.ImplicationGraph


cartesianProduct :: (a -> b -> c) -> [a] -> [b] -> [c]
cartesianProduct f as bs = [ f a b | a <- as, b <- bs ]


conjunction :: Edge -> Edge -> Edge
conjunction edge edge' =
  let
    onlyFreeVars = \case
      V.Bound _ _ -> Nothing
      var @ (V.Free path time _) -> Just (var, path, time)

    furthestVarMap mapping (var, path, time) =
      case (Map.lookup var (_edgeMap edge), Map.lookup path mapping) of
        (Just (V.Free _ time' _), _) -> Map.insert path time' mapping
        (Nothing, Just time') | time' > time -> Map.insert path time' mapping
        (Nothing, Just _) -> mapping
        _ -> Map.insert path time mapping

    bumpVarBy bumper = \case
      var @ (V.Free path time kind) -> case Map.lookup path bumper of
        Just bump -> V.Free path (time + bump) kind
        Nothing -> var
      other -> other

    conflicts = foldl furthestVarMap Map.empty
                $ mapMaybe onlyFreeVars
                $ Set.toList $ collectVars $ _edgeForm edge
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

