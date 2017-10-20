{-# LANGUAGE DeriveDataTypeable, TypeFamilies, TemplateHaskell, ConstraintKinds #-}
module Logic.ImplicationGraph.Type where

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Monad.Extra (whenM)
import           Control.Monad.Loops (orM, anyM)

import           Data.Data
import           Data.Ord.Graph (Graph)
import qualified Data.Ord.Graph as G
import qualified Data.Ord.Graph.Extras as G
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (mapMaybe, fromJust)
import           Data.List.Split (splitOn)
import           Data.Foldable (foldrM)

import           Logic.Formula
import           Logic.Model
import           Logic.Chc
import           Logic.Var
import qualified Logic.Solver.Z3 as Z3

import           Text.PrettyPrint.HughesPJClass
import           Text.Read (readMaybe)

data Vert idx
  = InstanceV [Var] Form
  | QueryV Form
  deriving (Show, Read, Eq, Ord, Data)
makePrisms ''Vert

data Edge = Edge Form (Map Var Var)
  deriving (Show, Read, Eq, Ord, Data)

instance Pretty Edge where
  pPrint (Edge f m) = pPrint f <+> pPrint (M.toList m)

instance Pretty idx => Pretty (Vert idx) where
  pPrint = \case
    InstanceV vs f -> pPrint vs <+> pPrint f
    QueryV f -> pPrint f

class (Show a, Ord a, Data a) => Idx a where
  type BaseIdx a
  baseIdx :: Lens' a (BaseIdx a)
  toPrefix :: a -> String
  fromPrefix :: String -> Maybe a
  inst :: Lens' a Integer

match :: (Idx a, Eq (BaseIdx a)) => a -> a -> Bool
match x y = x ^. baseIdx == y ^. baseIdx

data LinIdx = LinIdx { _linIden :: Integer, _linInst :: Integer }
  deriving (Show, Read, Eq, Data)
makeLenses ''LinIdx

instance Ord LinIdx where
  compare (LinIdx iden1 inst1) (LinIdx iden2 inst2) =
    case compare inst1 inst2 of
      LT -> GT
      GT -> LT
      EQ -> compare iden1 iden2

instance Idx LinIdx where
  type BaseIdx LinIdx = Integer
  baseIdx = linIden
  toPrefix (LinIdx iden i) = show iden ++ "_" ++ show i
  fromPrefix s = case splitOn "_" s of
      [iden, i] -> LinIdx <$> readMaybe iden <*> readMaybe i
      _ -> Nothing
  inst = linInst

instance Pretty LinIdx where
  pPrint (LinIdx iden i) = pPrint iden <+> pPrint i

type ImplGr idx = Graph idx Edge (Vert idx)

-- | Check whether the vertex labels in the graph form an inductive relationship.
isInductive :: (Eq (BaseIdx idx), Idx idx, MonadIO m) => idx -> ImplGr idx -> m Bool
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
              , allInd i (G.predecessors i g)
              ]) (g ^. at i)

    allInd i is = and <$> mapM (indPred i) is

    descendantInstanceVs i =
      G.descendants g i
        & filter (match i)
        & mapMaybe (\i' -> g ^? ix i' . _InstanceV . _2)

-- | Convert the graph into a system of Constrained Horn Clauses.
implGrChc :: Idx idx => ImplGr idx -> [Chc]
implGrChc g = concatMap idxRules (G.idxs g)
  where
    idxApp i = instApp i <$> g ^? ix i . _InstanceV
    instApp i (vs, _) = mkApp ('r' : toPrefix i) vs

    idxRules i = maybe [] (\case
      InstanceV _ _ ->
        mapMaybe (\(i', Edge f mvs) -> do
          lhs <- idxApp i'
          rhs <- subst mvs <$> idxApp i
          return (Rule [lhs] f rhs)) (relevantIncoming i)
      QueryV f -> queries i f) (g ^? ix i)

    queries i f =
      mapMaybe (\(i', Edge e mvs) -> do
        lhs <- idxApp i'
        let rhs = subst mvs f
        return (Query [lhs] e rhs)) (g ^@.. G.iedgesTo i)

    relevantIncoming i = g ^@.. G.iedgesTo i . indices (i >)

-- | Interpolate the facts in the graph using CHC solving to label the vertices
-- with fresh definitions.
interpolate :: (MonadIO m, Idx idx) => ImplGr idx -> m (Either Model (ImplGr idx))
interpolate g = Z3.solveChc (implGrChc g) >>= \case
    Left m -> return (Left m)
    Right m -> return (Right $ applyModel m g)

-- | Replace the fact at each vertex in the graph by the fact in the model.
applyModel :: Idx idx => Model -> ImplGr idx -> ImplGr idx
applyModel m = G.imapVerts applyVert
  where
    applyVert i = \case
      InstanceV vs _ ->
        let fact = M.findWithDefault (LBool True) i m'
        in InstanceV vs fact
      n -> n

    m' = M.mapKeys (interpretName . varName) $
           M.filterWithKey (\k _ -> head (varName k) == 'r') (getModel m)
      where
        interpretName ('r':rest) = fromJust $ fromPrefix rest
        interpretName _ = undefined

data Result idx
  = Failed Model
  | Complete (ImplGr idx)
  deriving (Show, Read, Eq)

type SolveState idx = Map (BaseIdx idx) Integer

type Solve idx m =
  (MonadError (Result idx) m, MonadState (SolveState idx) m, MonadIO m)

solve :: MonadIO m => LinIdx -> ImplGr LinIdx -> m (Either Model (ImplGr LinIdx))
solve end g =
  evalStateT (runExceptT (loop g)) M.empty >>= \case
    Left (Failed m) -> return (Left m)
    Left (Complete res) -> return (Right res)
    Right _ -> error "infinite loop terminated successfully?"
  where
    loop gr = loop =<< step end gr

step :: (Idx idx, Ord (BaseIdx idx), Eq (BaseIdx idx), Solve idx m)
     => idx -> ImplGr idx -> m (ImplGr idx)
step end g =
  interpolate g >>= either (throwError . Failed) (\interpolated ->
    whenM (isInductive end interpolated)
      (throwError $ Complete interpolated) >>
    foldrM (\((i1, i2), e) -> unfold i1 i2 e) g (G.backEdges g))

collectAnswer :: (Ord (BaseIdx idx), Idx idx)
              => ImplGr idx -> Map (BaseIdx idx) Form
collectAnswer g =
  execState (G.itravVerts (\i v -> case v of
    InstanceV _ f -> modify (M.insertWith mkOr (i ^. baseIdx) f)
    _ -> return ()) g) M.empty

unfold :: (Idx idx, Ord (BaseIdx idx), Solve idx m)
       => idx -> idx -> Edge -> ImplGr idx -> m (ImplGr idx)
unfold = G.unfold updateInstance (\_ _ -> return) (const return)

latestInstance :: (Idx idx, Ord (BaseIdx idx), MonadState (SolveState idx) m)
               => idx -> m idx
latestInstance idx = do
  i <- M.findWithDefault 0 (idx ^. baseIdx) <$> get
  return (idx & inst .~ i)

updateInstance :: (Idx idx, Ord (BaseIdx idx), MonadState (SolveState idx) m) => idx -> m idx
updateInstance idx = do
  res <- latestInstance idx
  let res' = res & inst +~ 1
  at (idx ^. baseIdx) ?= (res' ^. inst)
  return res'

emptyImplGr :: ImplGr ix
emptyImplGr = G.empty

emptyInst :: Idx idx => idx -> [Var] -> ImplGr idx -> ImplGr idx
emptyInst i vs = G.addVert i (InstanceV vs (LBool True))

query :: Idx idx => idx -> Form -> ImplGr idx -> ImplGr idx
query i f = G.addVert i (QueryV f)

edge :: Idx idx => idx -> idx -> Form -> Map Var Var -> ImplGr idx -> ImplGr idx
edge i1 i2 f m = G.addEdge i1 i2 (Edge f m)

-- connAnd :: Idx idx => [idx] -> idx -> Form -> Map Var Var -> ImplGr idx -> ImplGr idx
-- connAnd is i f m g =
--   foldr (\(i', f', m') -> G.addEdge i' i (Edge f' m'))
--         (g & ix i . _InstanceV %~ AndInst is)
--         (zip3 is (f:repeat (LBool True)) (m:repeat M.empty))

-- connOr :: Idx idx => [[idx]] -> idx -> ImplGr idx -> ImplGr idx
-- connOr is i = ix i . _InstanceV %~ OrInst is
