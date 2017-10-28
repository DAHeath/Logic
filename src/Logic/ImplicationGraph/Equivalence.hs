{-# LANGUAGE TemplateHaskell, TypeFamilies #-}
module Logic.ImplicationGraph.Equivalence where

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Monad.Extra (whenM, orM, anyM)

import           Data.Data (Data)
import           Data.Maybe (mapMaybe)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.List.Split (splitOn)
import qualified Data.Optic.Graph as G
import qualified Data.Optic.Graph.Extras as G
import           Data.Text.Prettyprint.Doc

import qualified Logic.Type as T
import           Logic.Formula
import           Logic.Var
import           Logic.Model
import           Logic.ImplicationGraph hiding (isInductive)
import qualified Logic.Solver.Z3 as Z3

import           Text.Read (readMaybe)

data PIdx = PIdx { _idx1 :: LinIdx, _idx2 :: LinIdx }
  deriving (Show, Read, Eq, Ord, Data)
makeLenses ''PIdx

equivalence :: MonadIO m
            => [(Var, Var)] -> [(Var, Var)] -> PIdx -> ImplGr LinIdx -> ImplGr LinIdx
            -> m (Either Model (Map (Integer, Integer) Form))
equivalence st st' end g1 g2 =
  evalStateT (runExceptT (equiv st st' end g1 g2)) M.empty >>= \case
    Left (Failed m) -> return (Left m)
    Left (Complete res) -> do
      G.display "test" res
      return (Right $ collectAnswer res)
    Right _ -> error "infinite loop terminated successfully?"


equiv :: Solve PIdx m
      => [(Var, Var)] -> [(Var, Var)] -> PIdx -> ImplGr LinIdx -> ImplGr LinIdx -> m ()
equiv st st' end g1 g2 =
  let pr = equivProduct g1 g2
      quer = end & idx1 . linIden +~ 1
      init =
        G.addEdge end quer (Edge (LBool True) M.empty) $
        G.addVert quer (QueryV
          (app2 Impl (manyAnd (map equate st))
                     (manyAnd (map equate st')))) pr
  in interpolate init >>= either (throwError . Failed) (\interp -> do
      whenM (isInductive quer interp) (throwError $ Complete interp)
      g1' <- unwindAllBackEdges g1
      g2' <- unwindAllBackEdges g2
      equiv st st' end g1' g2')
  where
    equate (v1, v2) = mkEql (T.typeOf v1) (V v1) (V v2)

-- | Check whether the vertex labels in the graph form an inductive relationship.
isInductive :: MonadIO m => PIdx -> ImplGr PIdx -> m Bool
isInductive start g = evalStateT (ind start) M.empty
  where
    ind i = maybe (computeInd i) return . M.lookup i =<< get
    indPred i i' = if i <= i' then return False else ind i'

    computeInd i =
      (ix i <.=) =<< maybe (return False) (\case
        QueryV _ -> allInd i (G.predecessors i g)
        InstanceV _ f ->
          orM [ return $ f == LBool True
              , anyM (`Z3.entails` f) (descendantInstanceVs i)
              , allInd i (lpredecessors i g)
              , allInd i (rpredecessors i g)
              ]) (g ^. at i)

    allInd i is = and <$> mapM (indPred i) is

    lpredecessors i g = filter (\i' -> i == i' || i' ^. idx1 < i ^. idx1) $ G.predecessors i g
    rpredecessors i g = filter (\i' -> i == i' || i' ^. idx1 >= i ^. idx1) $ G.predecessors i g

    descendantInstanceVs i =
      G.descendants g i
        & filter (match i)
        & mapMaybe (\i' -> g ^? ix i' . _InstanceV . _2)

equivProduct :: ImplGr LinIdx -> ImplGr LinIdx -> ImplGr PIdx
equivProduct = G.cartesianProduct PIdx merge

merge :: Vert -> Vert -> Vert
merge v1 v2 = case (v1, v2) of
  (InstanceV vs1 _, InstanceV vs2 _) -> emptyInst (vs1 ++ vs2)
  _ -> error "query in middle of equivalence graph"

instance Idx PIdx where
  type BaseIdx PIdx = (Integer, Integer)
  baseIdx = lens getBase setBase
    where
      getBase (PIdx (LinIdx a _) (LinIdx c _)) = (a, c)
      setBase (PIdx (LinIdx _ b) (LinIdx _ d)) (a, c) = PIdx (LinIdx a b) (LinIdx c d)
  written = prism' toWr fromWr
    where
      toWr (PIdx i1 i2) = written # i1 ++ "_" ++ written # i2
      fromWr s = case splitOn "_" s of
        [a, b, c, d] -> PIdx <$> ((a ++ "_" ++ b) ^? written)
                             <*> ((c ++ "_" ++ d) ^? written)
        _ -> Nothing

instance Pretty PIdx where
  pretty (PIdx i1 i2) = pretty i1 <+> pretty i2
