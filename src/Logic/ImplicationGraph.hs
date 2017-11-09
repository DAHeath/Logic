{-# LANGUAGE DeriveDataTypeable, TypeFamilies, TemplateHaskell, ConstraintKinds #-}
module Logic.ImplicationGraph where

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Monad.Loops (anyM)

import           Data.Data
import           Data.Optic.Graph (Graph)
import qualified Data.Optic.Graph as G
import qualified Data.Optic.Graph.Extras as G
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (mapMaybe, catMaybes)
import           Data.List.Split (splitOn)
import           Data.Foldable (foldrM)
import           Data.Text.Prettyprint.Doc

import           Logic.Formula
import           Logic.Model
import           Logic.Chc
import           Logic.Var
import qualified Logic.Solver.Z3 as Z3

import           Text.Read (readMaybe)

data Vert
  = InstanceV [Var] Form
  | QueryV Form
  deriving (Show, Read, Eq, Ord, Data)
makePrisms ''Vert

emptyInst :: [Var] -> Vert
emptyInst vs = InstanceV vs (LBool False)

data Edge = Edge
  { _edgeForm :: Form
  , _edgeMap :: Map Var Var
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Edge

instance Pretty Edge where
  pretty (Edge f m) = pretty f <+> pretty (M.toList m)

instance Pretty Vert where
  pretty = \case
    InstanceV vs f -> pretty vs <+> pretty f
    QueryV f -> pretty f

data Idx = Idx { _idxIden :: Integer, _idxInst :: Integer }
  deriving (Show, Read, Eq, Data)
makeLenses ''Idx

firstInst :: Integer -> Idx
firstInst i = Idx i 0

match :: Idx -> Idx -> Bool
match x y = x ^. idxIden == y ^. idxIden

instance Ord Idx where
  compare (Idx iden1 inst1) (Idx iden2 inst2) =
    case compare inst1 inst2 of
      LT -> GT
      GT -> LT
      EQ -> compare iden1 iden2

written :: Prism' String Idx
written = prism' toWritten fromWritten
  where
    toWritten (Idx iden i) = show iden ++ "_" ++ show i
    fromWritten s = case splitOn "_" s of
        [iden, i] -> Idx <$> readMaybe iden <*> readMaybe i
        _ -> Nothing

instance Pretty Idx where
  pretty (Idx iden i) = pretty iden <+> pretty i

type ImplGr idx = Graph idx Edge Vert

-- | Convert the graph into a system of Constrained Horn Clauses.
implGrChc :: ImplGr Idx -> [Chc]
implGrChc g = concatMap idxRules (G.idxs g)
  where
    idxApp i = instApp i =<< g ^? ix i . _InstanceV
    instApp _ ([], _) = Nothing
    instApp i (vs, _) = Just $ mkApp ('r' : written # i) vs

    idxRule i f rhs = vertRule i f rhs <$> g ^? ix i
    vertRule i f rhs = \case
      InstanceV [] _   -> Rule [] f rhs
      InstanceV vs _   -> Rule [mkApp ('r':written # i) vs] f rhs
      QueryV _         -> undefined

    idxRules i = maybe [] (\case
      InstanceV _ _ ->
        mapMaybe (\(i', Edge f mvs) -> do
          rhs <- subst mvs <$> idxApp i
          idxRule i' f rhs) (relevantIncoming i)
      QueryV f -> queries i f) (g ^? ix i)

    queries i f =
      mapMaybe (\(i', Edge e mvs) -> do
        lhs <- idxApp i'
        let rhs = subst mvs f
        return (Query [lhs] e rhs)) (g ^@.. G.iedgesTo i)

    -- We only create rules for non-back edges
    relevantIncoming i = g ^@.. G.iedgesTo i . indices (i >)

-- | Interpolate the facts in the graph using CHC solving to label the vertices
-- with fresh definitions.
interpolate :: MonadIO m => ImplGr Idx -> m (Either Model (ImplGr Idx))
interpolate g = (fmap . fmap) (`applyModel` g) (Z3.solveChc (implGrChc g))

-- | Augment the fact at each vertex in the graph by the fact in the model.
applyModel :: Model -> ImplGr Idx -> ImplGr Idx
applyModel m = G.imapVerts applyVert
  where
    applyVert i = _InstanceV %~ applyInst i
    applyInst i inst =
      inst & _2 .~ instantiate (fst inst) (M.findWithDefault (LBool False) i m')

    m' = M.toList (getModel m)
      & map (traverseOf _1 %%~ interpretName . varName)
      & catMaybes & M.fromList
      where interpretName n = n ^? to uncons . _Just . _2 . written

data Result e
  = Failed Model
  | Complete (Graph Idx e Vert)
  deriving (Show, Read, Eq)

type SolveState = Map Integer Integer

type Solve e m =
  (MonadError (Result e) m, MonadState SolveState m, MonadIO m)

runSolve :: Monad m => ExceptT e (StateT (Map k a) m) a1 -> m (Either e a1)
runSolve ac = evalStateT (runExceptT ac) M.empty

-- | Gather all facts known about each instance of the same index together by disjunction.
collectAnswer :: MonadIO m => ImplGr Idx -> m (Map Integer Form)
collectAnswer g = traverse Z3.superSimplify $ execState (G.itravVerts (\i v -> case v of
  InstanceV _ f ->
    if f == LBool True then return ()
    else modify (M.insertWith mkOr (i ^. idxIden) f)
  _ -> return ()) g) M.empty

-- | Unwind the graph on the given backedge and update all instances in the unwinding.
unwind :: Solve e m => Idx -> Idx -> e -> Graph Idx e Vert -> m (Idx, Graph Idx e Vert)
unwind = G.unwind updateInstance (\_ _ -> return)
  (\_ v -> return $ v & _InstanceV . _2 .~ LBool False)

unwindAll :: Solve e m
          => [((Idx, Idx), e)]
          -> [Idx] -> Idx
          -> Graph Idx e Vert -> m (Graph Idx e Vert)
unwindAll bes ind end g = do
  (is, g') <- foldrM (\((i1, i2), e) (is, g') ->
    if any (`elem` ind) (G.idxs (G.reached i1 (G.withoutBackEdges g')))
    then return (is, g')
    else do (i, g'') <- unwind i1 i2 e g'
            return (i:is, g'')) ([], g) bes
  let g'' = G.ifilterEdges (\i1 i2 _ -> (i1, i2) `notElem` map fst bes) g'
  return (reachEndWithoutBackedge g'')
  where
    reachEndWithoutBackedge g' =
      let compressed = g'
            & G.ifilterEdges (\i1 i2 _ -> (i1, i2) `notElem` map fst (G.backEdges g'))
            & G.reaches end
      in G.filterIdxs (`elem` G.idxs compressed) g'

-- | Find a fresh instance counter for the given index.
updateInstance :: MonadState SolveState m => Idx -> m Idx
updateInstance idx = flip (set idxInst) idx <$> (at (idx ^. idxIden) . non 0 <+= 1)
