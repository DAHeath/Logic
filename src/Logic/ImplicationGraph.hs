{-# LANGUAGE DeriveDataTypeable, TypeFamilies, TemplateHaskell, ConstraintKinds #-}
module Logic.ImplicationGraph where

import           Control.Lens
import           Control.Arrow ((***))
import           Control.Applicative.Backwards
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Monad.Loops (anyM)

import           Data.Data
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G
import qualified Data.Optic.Graph.Extras as G
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Maybe (catMaybes, fromJust)
import           Data.List.Split (splitOn)
import           Data.List (find)
import           Data.Foldable (foldrM, fold)
import           Data.Text.Prettyprint.Doc

import           Logic.Formula
import           Logic.Model
import           Logic.Var
import qualified Logic.Solver.Z3 as Z3

import           Text.Read (readMaybe)

import Debug.Trace

type Idx = Integer
type Loc = Integer

data Vert = Vert
  { _vertLoc :: Loc
  , _vertVars :: [Var]
  , _vertForm :: Form
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Vert

data Edge = Edge
  { _edgeForm :: Form
  , _edgeMap :: Map Var Var
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Edge

type ImplGr e = Graph Idx e Vert

fromGraph :: (Show e, AsInteger i) => Graph i e Vert -> ImplGr e
fromGraph g = evalState (setIdxs g) 0
  where
    setIdxs g = do
      m <- buildMapping
      return (G.mapIdx (m M.!) g)
      where
        buildMapping =
          let noBacks = G.ifilterEdges (\i _ -> i `notElem` map fst (G.backEdges g)) g
          in
          execStateT (
            forwards $ fromJust (G.itopVert_ (\i -> Backwards . update i) noBacks)) M.empty
        update i _ = modify . M.insert i =<< lift freshIdx
        freshIdx = state (\ins -> (ins, ins+1))

class (Show a, Ord a) => AsInteger a where asInteger :: a -> Integer
instance AsInteger Integer where asInteger = id

emptyInst :: Loc -> [Var] -> Vert
emptyInst l vs = Vert l vs (LBool False)

instance Pretty Edge where
  pretty (Edge f m) = pretty f <+> pretty (M.toList m)

instance Pretty Vert where
  pretty (Vert l vs f) = pretty l <+> pretty vs <+> pretty f

-- | Augment the fact at each vertex in the graph by the fact in the model.
applyModel :: Model -> ImplGr Edge -> ImplGr Edge
applyModel m = G.imapVert applyVert
  where
    applyVert i v = v & vertForm %~ (\f -> M.findWithDefault f i m')

    m' = M.toList (getModel m)
      & map (traverseOf _1 %%~ interpretName . varName)
      & catMaybes & M.fromList
      where interpretName n = n ^? to uncons . _Just . _2 . _Show

data Result e
  = Failed Model
  | Complete (ImplGr e)
  deriving (Show, Read, Eq)

type Solve e m = (MonadError (Result e) m, MonadIO m)

runSolve :: Monad m => ExceptT e (StateT Integer m) a1 -> m (Either e a1)
runSolve ac = evalStateT (runExceptT ac) 0

-- | Gather all facts known about each instance of the same index together by disjunction.
-- collectAnswer :: MonadIO m => ImplGr Edge -> m (Map Integer Form)
-- collectAnswer g = traverse Z3.superSimplify $ execState (G.itravVerts (\i v -> case v of
--   InstanceV _ f ->
--     if f == LBool True then return ()
--     else modify (M.insertWith mkOr (i ^. idxIden) f)
--   _ -> return ()) (g ^. implGr)) M.empty

relabel :: (MonadState Integer m) => Idx -> Graph Idx e v -> m (Idx, Graph Idx e v)
relabel end g = do
  m <- buildMapping
  return (M.findWithDefault end end m, G.mapIdx (\i -> M.findWithDefault i i m) g)
  where
    buildMapping =
      let noBacks = G.ifilterEdges (\i _ -> i `notElem` map fst (revBackEdges g)) g
          revSubGr = G.reaches end noBacks
      in
      execStateT (
        forwards $ fromJust (G.itopVert_ (\i -> Backwards . update i) revSubGr)) M.empty

    update i _ = do
      f <- lift freshIdx
      modify $ M.insert i f
    freshIdx = state (\ins -> (ins, ins+1))

-- | Unwind all backedges which do not reach an inductive vertex, then compress
-- the graph to only those vertices which reach the end.
unwindAll :: [(G.HEdge Idx, e)] -> [Idx] -> Idx -> ImplGr e -> ImplGr e
unwindAll bes ind end ig =
  traceShow (map fst bes) $
  let relevantBes = filter (\(G.HEdge i _, _) ->
        any (\i' -> all (`notElem` ind) (ig & withoutRevBackEdges & G.reached i' & G.idxs)) i) bes
      (is, ig') =
        foldr (\(G.HEdge i1 i2, e) (is, ig) ->
          let (i, ig') = unwind i1 i2 e ig
          in (i:is, ig')) ([], ig) relevantBes
  in ig' & G.ifilterEdges (\i _ -> i `notElem` map fst bes)
         & reachEndWithoutBackedge
  where
    reachEndWithoutBackedge g' =
      let compressed = g'
            & G.ifilterEdges (\i _ -> i `notElem` map fst (revBackEdges g'))
            & G.reaches end
      in G.filterIdxs (`elem` G.idxs compressed) g'

-- | Unwind the graph on the given backedge and update all instances in the unwinding.
unwind :: Set Idx -> Idx -> e -> ImplGr e -> ([Idx], ImplGr e)
unwind i1 i2 e g =
  let g' = (G.reaches i2 (G.delEdge (G.HEdge i1 i2) g)
              `mappend` foldMap (\i -> G.between i2 i g) i1)
         & G.mapVert (vertForm .~ LBool False)
      ((i1', g''), lbl') =
        runState (foldrM (\i (is, g) -> do
          (i', g') <- relabel i g
          return (i' : is, g')) ([], g') i1) (G.order g)
  in
  (i1', g & (G.addEdge (G.HEdge (S.fromList i1') i2) e . mappend g''))

newtype ReverseOrder a = ReverseOrder { getReverseOrder :: a }
  deriving (Show, Read, Eq, Data)
instance Ord a => Ord (ReverseOrder a) where
  ReverseOrder a <= ReverseOrder b = b <= a

revBackEdges :: Ord i => Graph i e v -> [(G.HEdge i, e)]
revBackEdges = map (\(G.HEdge i1 i2, e) -> (G.HEdge (G.omap getReverseOrder i1) (getReverseOrder i2), e))
             . G.backEdges
             . G.mapIdx ReverseOrder

withoutRevBackEdges :: Ord i => Graph i e v -> Graph i e v
withoutRevBackEdges = G.mapIdx getReverseOrder . G.withoutBackEdges . G.mapIdx ReverseOrder
