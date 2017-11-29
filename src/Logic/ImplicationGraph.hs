{-# LANGUAGE DeriveDataTypeable, TypeFamilies, TemplateHaskell, ConstraintKinds #-}
module Logic.ImplicationGraph where

import           Control.Lens
import           Control.Arrow (first)
import           Control.Applicative.Backwards
import           Control.Monad.State

import           Data.Data
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Maybe (fromJust)
import           Data.Text.Prettyprint.Doc

import           Logic.Formula
import           Logic.Model
import           Logic.Var
import qualified Logic.Solver.Z3 as Z3

-- | Inst indexes are arranged backwards -- newer instances which occur
-- closer to the beginning of the graph have higher value.
newtype Idx = Idx { getIdx :: Integer }
  deriving (Eq, Data, Num, Pretty)
instance Ord Idx where Idx a <= Idx b = b <= a
instance Show Idx where show (Idx a) = show a
instance Read Idx where readsPrec i = map (first Idx) . readsPrec i

type Loc = Integer

data Inst = Inst
  { _instLoc :: Loc
  , _instVars :: [Var]
  , _instForm :: Form
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Inst

data Edge = Edge
  { _edgeForm :: Form
  , _edgeMap :: Map Var Var
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Edge

instance Pretty Edge where
  pretty (Edge f m) = pretty f <+> pretty (M.toList m)

instance Pretty Inst where
  pretty (Inst l vs f) = pretty l <+> pretty vs <+> pretty f

type ImplGr e = Graph Idx e Inst

-- | Construct an implication graph by swapping the labels for proper instance labels.
fromGraph :: Ord i => Graph i e Inst -> ImplGr e
fromGraph g = snd $ relabel (Idx 0) g

-- | An instance which contains no formula.
emptyInst :: Loc -> [Var] -> Inst
emptyInst l vs = Inst l vs (LBool False)

-- | Gather all facts known about each instance of the same index together by disjunction.
collectAnswer :: MonadIO m => ImplGr Edge -> m (Map Integer Form)
collectAnswer g = traverse Z3.superSimplify $ execState (G.itravVert (\_ (Inst loc _ f) ->
  when (f /= LBool True) $ modify (M.insertWith mkOr loc f)) g) M.empty

-- | Unwind all backedges which do not reach an inductive vertex, then compress
-- the graph to only those vertices which reach the end.
unwindAll :: [(G.HEdge Idx, e)] -> Set Idx -> Idx -> ImplGr e -> ImplGr e
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
    buildMapping g =         -- To construct the relabelling map
      g & G.withoutBackEdges -- consider the graph without backedges
        & G.itopVert_ update -- update the map in topological order
        & fromJust           -- we know there are no backedges since we removed them
        & forwards           -- run the updates forwards

    -- add an entry to the relabelling map (in backwards order)
    update i _ = Backwards (modify . M.insert i =<< lift freshIdx)

    -- use the state to create a fresh index
    freshIdx = state (\ins -> (ins, ins+1))
