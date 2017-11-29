{-# LANGUAGE DeriveDataTypeable, TypeFamilies, TemplateHaskell, ConstraintKinds #-}
module Logic.ImplicationGraph where

import           Control.Lens
import           Control.Arrow ((***), first)
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

-- | Instance indexes are arranged backwards -- newer instances which occur
-- closer to the beginning of the graph have higher value.
newtype Idx = Idx { getIdx :: Integer }
  deriving (Eq, Data, Num, Pretty)
instance Ord Idx where Idx a <= Idx b = b <= a
instance Show Idx where show (Idx a) = show a
instance Read Idx where readsPrec i = map (first Idx) . readsPrec i

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

instance Pretty Edge where
  pretty (Edge f m) = pretty f <+> pretty (M.toList m)

instance Pretty Vert where
  pretty (Vert l vs f) = pretty l <+> pretty vs <+> pretty f

type ImplGr e = Graph Idx e Vert

-- | Construct an implication graph by swapping the labels for proper instance labels.
fromGraph :: Ord i => Graph i e Vert -> ImplGr e
fromGraph g = snd $ relabel (Idx 0) g

emptyInst :: Loc -> [Var] -> Vert
emptyInst l vs = Vert l vs (LBool False)

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

-- | Unwind all backedges which do not reach an inductive vertex, then compress
-- the graph to only those vertices which reach the end.
unwindAll :: [(G.HEdge Idx, e)] -> [Idx] -> Idx -> ImplGr e -> ImplGr e
unwindAll bes ind end g =
  let relevantBes = bes & filter (\be ->        -- a backedge is relevant if...
        be & fst & G.start                      -- we consider the start of the backedge and...
           & any (\i' -> g & G.withoutBackEdges -- when there are no backedges...
                           & G.reached i'       -- the subgraph reached by the start of the backedge...
                           & G.idxs             -- contains no inductive indices
                           & none (`elem` ind)))
  in g & flip (foldr unwind) relevantBes                  -- unwind all the relevant backedges
       & G.ifilterEdges (\i _ -> i `notElem` map fst bes) -- filter out the old backedges
       & reachEndWithoutBackedge                          -- select the portion which reaches the query
       & relabel (Idx 0) & snd                            -- relabel to account for discarded indices
  where
    reachEndWithoutBackedge g' =
      let compressed = g'        -- find the subgraph which...
            & G.withoutBackEdges -- has no backedges...
            & G.reaches end      -- and reaches the query
      in G.filterIdxs (`elem` G.idxs compressed) g'

-- | Unwind the graph on the given backedge and update all instances in the unwinding.
unwind :: (G.HEdge Idx, e) -> ImplGr e -> ImplGr e
unwind (G.HEdge i1 i2, e) g =
  let (m, g') = g                                       -- in order to calculate the unwound subgraph:
        & G.reaches i2                                  -- find the subgraph which reaches the end of backedge
        & G.union (foldMap (\i -> G.between i2 i g) i1) -- attach the subgraph between the ends of the backedge
        & relabel (Idx $ G.order g)                     -- relabel all the instances
  in
  g & G.union g'                                  -- attach the unwound subgraph
    & G.delEdge (G.HEdge i1 i2)                   -- delete the old backedge
    & G.addEdge (G.HEdge (S.map (m M.!) i1) i2) e -- re-add the backedge as a forward edge from the unwound subgraph

-- | Relabel the vertices in the graph in reverse topological order. The new index
-- values are obtained from the state. The map used to relabel is also returned.
relabel :: Ord i => Idx -> Graph i e v -> (Map i Idx, Graph Idx e v)
relabel idx g = evalState (do
  m <- execStateT (buildMapping g) M.empty
  return (m, G.mapIdx (m M.!) g)) idx
  where
    buildMapping = forwards . fromJust . G.itopVert_ update . G.withoutBackEdges
    update i _ = Backwards (modify . M.insert i =<< lift freshIdx)
    freshIdx = state (\ins -> (ins, ins+1))

