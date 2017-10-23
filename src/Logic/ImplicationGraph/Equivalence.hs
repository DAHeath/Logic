{-# LANGUAGE TemplateHaskell, TypeFamilies #-}
module Logic.ImplicationGraph.Equivalence where

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Monad.Extra (whenM)

import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.List.Split (splitOn)
import qualified Data.Ord.Graph as G
import qualified Data.Ord.Graph.Extras as G
import           Data.Text.Prettyprint.Doc

import           Logic.Formula
import           Logic.Model
import           Logic.ImplicationGraph

import           Text.Read (readMaybe)

equivalence :: MonadIO m => ImplGr LinIdx -> ImplGr LinIdx
            -> m (Either Model (Map (Integer, Integer) Form))
equivalence g1 g2 =
  undefined

equiv :: Solve PIdx m => PIdx -> ImplGr LinIdx -> ImplGr LinIdx -> m ()
equiv end g1 g2 =
  let pr = equivProduct g1 g2
  in interpolate pr >>= either (throwError . Failed) (\interp -> do
    whenM (isInductive end interp) (throwError $ Complete interp)
    g1' <- unwindAllBackEdges g1
    g2' <- unwindAllBackEdges g2
    equiv end g1' g2')

equivProduct :: ImplGr LinIdx -> ImplGr LinIdx -> ImplGr PIdx
equivProduct g1 g2 =
  setup $ G.cartesianProduct PIdx merge g1 g2

setup :: ImplGr PIdx -> ImplGr PIdx
setup = id

merge :: Vert -> Vert -> Vert
merge v1 v2 = case (v1, v2) of
  (InstanceV vs1 _, InstanceV vs2 _) -> emptyInst (vs1 ++ vs2)
  _ -> error "query in middle of equivalence graph"

data PIdx = PIdx { _idx1 :: LinIdx, _idx2 :: LinIdx }
  deriving (Show, Read, Eq, Ord, Data)
makeLenses ''PIdx

instance Idx PIdx where
  type BaseIdx PIdx = (Integer, Integer)
  baseIdx = lens getBase setBase
    where
      getBase (PIdx (LinIdx a _) (LinIdx c _)) = (a, c)
      setBase (PIdx (LinIdx _ b) (LinIdx _ d)) (a, c) = PIdx (LinIdx a b) (LinIdx c d)
  written = prism' toWr fromWr
    where
      toWr (PIdx i1 i2) = show i1 ++ "_" ++ show i2
      fromWr s = case splitOn "_" s of
        [a, b, c, d] -> PIdx <$> (LinIdx <$> readMaybe a <*> readMaybe b)
                             <*> (LinIdx <$> readMaybe c <*> readMaybe d)
        _ -> Nothing

instance Pretty PIdx where
  pretty (PIdx i1 i2) = pretty i1 <+> pretty i2
