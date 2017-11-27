{-# LANGUAGE DeriveDataTypeable, TypeFamilies, TemplateHaskell, ConstraintKinds #-}
module Logic.ImplicationGraph where

import           Control.Lens
import           Control.Arrow ((***))
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Monad.Loops (anyM)

import           Data.Data
import           Data.Optic.Directed.Graph (Graph)
import qualified Data.Optic.Directed.Graph as G
import qualified Data.Optic.Graph.Extras as G
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (catMaybes, fromJust)
import           Data.List.Split (splitOn)
import           Data.List (find)
import           Data.Foldable (foldrM)
import           Data.Text.Prettyprint.Doc

import           Logic.Formula
import           Logic.Model
import           Logic.Var
import qualified Logic.Solver.Z3 as Z3

import           Text.Read (readMaybe)

type Idx = Integer
type Loc = Integer

data Vert
  = InstanceV Loc [Var] Form
  | QueryV Form
  deriving (Show, Read, Eq, Ord, Data)
makePrisms ''Vert

data Edge = Edge
  { _edgeForm :: Form
  , _edgeMap :: Map Var Var
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Edge

type HyperEdges = Map Loc [(Loc, Loc)]

data ImplGr edge = ImplGr
  { _implGr :: Graph Idx edge Vert
  , _hyperEdges :: HyperEdges
  , _entrance :: Loc
  , _exit :: Idx
  , _currIdx :: Idx
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''ImplGr

fromGraph :: AsInteger i => HyperEdges -> Graph i e Vert -> Maybe (ImplGr e)
fromGraph hes g =
  case theQuery of
    Nothing -> Nothing
    Just q ->
      let ((q', g'), lbl) = runState (setIdxs q g) 0
          theEntry = minimum $ G.idxs g'
      in Just (ImplGr g' hes theEntry q' lbl)
  where
    theQuery = fst <$> (g ^@? G.iallVerts . _QueryV)

    setIdxs end g = do
      m <- buildMapping
      return (m M.! end, G.mapIdx (m M.!) g)
      where
        buildMapping =
          let noBacks = G.ifilterEdges (\i _ -> i `notElem` map fst (G.backEdges g)) g
              revSubGr = G.reached end $ G.reverse noBacks
          in
          execStateT (fromJust (G.itopVert_ update revSubGr)) M.empty
        update i _ = modify . M.insert i =<< lift freshIdx
        freshIdx = state (\ins -> (ins, ins+1))

class (Show a, Ord a) => AsInteger a where asInteger :: a -> Integer
instance AsInteger Integer where asInteger = id

type instance Index (ImplGr e) = Idx
type instance IxValue (ImplGr e) = Vert
instance Ixed (ImplGr e)
instance At (ImplGr e) where at i = implGr . at i

emptyInst :: Loc -> [Var] -> Vert
emptyInst l vs = InstanceV l vs (LBool False)

instance Pretty Edge where
  pretty (Edge f m) = pretty f <+> pretty (M.toList m)

instance Pretty Vert where
  pretty = \case
    InstanceV l vs f -> pretty l <+> pretty vs <+> pretty f
    QueryV f -> pretty f

-- | Augment the fact at each vertex in the graph by the fact in the model.
applyModel :: Model -> ImplGr Edge -> ImplGr Edge
applyModel m = implGr %~ G.imapVert applyVert
  where
    applyVert i = _InstanceV %~ applyInst i
    applyInst i inst =
      inst & _3 .~ instantiate (inst ^. _2) (M.findWithDefault (LBool False) i m')

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
  return (m M.! end, G.mapIdx (\i -> M.findWithDefault i i m) g)
  where
    buildMapping =
      let noBacks = G.ifilterEdges (\i _ -> i `notElem` map fst (revBackEdges g)) g
          revSubGr = G.reached end $ G.reverse noBacks
      in
      execStateT (fromJust (G.itopVert_ update revSubGr)) M.empty

    update i _ = modify . M.insert i =<< lift freshIdx
    freshIdx = state (\ins -> (ins, ins+1))

-- | Unwind all backedges which do not reach an inductive vertex, then compress
-- the graph to only those vertices which reach the end.
unwindAll :: [(G.Pair Idx, e)] -> [Idx] -> Idx -> ImplGr e -> ImplGr e
unwindAll bes ind end ig =
  let relevantBes = filter (\(G.Pair i1 _, _) ->
        all (`notElem` ind) (ig ^. implGr & withoutRevBackEdges & G.reached i1 & G.idxs)) bes
      (is, ig') =
        foldr (\(G.Pair i1 i2, e) (is, ig) ->
          let (i, ig') = unwind i1 i2 e ig
          in (i:is, ig')) ([], ig) relevantBes
  in ig' & implGr %~ G.ifilterEdges (\i _ -> i `notElem` map fst bes)
         & implGr %~ reachEndWithoutBackedge
  where
    reachEndWithoutBackedge g' =
      let compressed = g'
            & G.ifilterEdges (\i _ -> i `notElem` map fst (revBackEdges g'))
            & G.reaches end
      in G.filterIdxs (`elem` G.idxs compressed) g'

-- | Unwind the graph on the given backedge and update all instances in the unwinding.
unwind :: Idx -> Idx -> e -> ImplGr e -> (Idx, ImplGr e)
unwind i1 i2 e ig =
  let g = ig ^. implGr
      g' = (G.reaches i2 (G.delEdge (G.Pair i1 i2) g) `mappend` G.between i2 i1 g)
         & G.mapVert (_InstanceV . _3 .~ LBool False)
      ((i1', g''), lbl') = runState (relabel i1 g') (ig ^. currIdx)
  in
  (i1', ig & currIdx .~ lbl' & implGr %~ (G.addEdge (G.Pair i1' i2) e . mappend g''))

newtype ReverseOrder a = ReverseOrder { getReverseOrder :: a }
  deriving (Show, Read, Eq, Data)
instance Ord a => Ord (ReverseOrder a) where
  ReverseOrder a <= ReverseOrder b = b <= a

revBackEdges :: Ord i => Graph i e v -> [(G.Pair i, e)]
revBackEdges = map (\(G.Pair i1 i2, e) -> (G.Pair (getReverseOrder i1) (getReverseOrder i2), e))
             . G.backEdges
             . G.mapIdx ReverseOrder

withoutRevBackEdges :: Ord i => Graph i e v -> Graph i e v
withoutRevBackEdges = G.mapIdx getReverseOrder . G.withoutBackEdges . G.mapIdx ReverseOrder
