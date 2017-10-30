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

data Edge = Edge Form (Map Var Var)
  deriving (Show, Read, Eq, Ord, Data)

instance Pretty Edge where
  pretty (Edge f m) = pretty f <+> pretty (M.toList m)

instance Pretty Vert where
  pretty = \case
    InstanceV vs f -> pretty vs <+> pretty f
    QueryV f -> pretty f

class (Show a, Ord a, Data a) => Idx a where
  type BaseIdx a
  baseIdx :: Lens' a (BaseIdx a)
  written :: Prism' String a

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
  written = prism' toWritten fromWritten
    where
      toWritten (LinIdx iden i) = show iden ++ "_" ++ show i
      fromWritten s = case splitOn "_" s of
          [iden, i] -> LinIdx <$> readMaybe iden <*> readMaybe i
          _ -> Nothing

instance Pretty LinIdx where
  pretty (LinIdx iden i) = pretty iden <+> pretty i

type ImplGr idx = Graph idx Edge Vert

-- | Check whether the vertex labels in the graph form an inductive relationship.
inductive :: (Eq (BaseIdx idx), Idx idx, MonadIO m, Pretty idx) => idx -> ImplGr idx -> m (Map idx Bool)
inductive start g = execStateT (ind start) M.empty
  where
    ind i = maybe (computeInd i) return . M.lookup i =<< get
    indPred i i' = if i <= i' then return False else ind i'

    computeInd i =
      (at i <?=) =<< maybe (return False) (\v -> do
        psInd <- allInd i (G.predecessors i g)
        case v of
          QueryV _ -> return psInd
          InstanceV _ f ->
            or <$> sequence [ return $ f == LBool True
                            , return psInd
                            , anyM (`Z3.entails` f) (descendantInstanceVs i)
                            ]) (g ^. at i)

    allInd i is = and <$> mapM (indPred i) is

    descendantInstanceVs i =
      G.descendants i g
        & filter (match i)
        & filter (/= i)
        & mapMaybe (\i' -> g ^? ix i' . _InstanceV . _2)

-- | Convert the graph into a system of Constrained Horn Clauses.
implGrChc :: Idx idx => ImplGr idx -> [Chc]
implGrChc g = concatMap idxRules (G.idxs g)
  where
    idxApp i = instApp i =<< g ^? ix i . _InstanceV
    instApp _ ([], _) = Nothing
    instApp i (vs, _) = Just $ mkApp ('r' : written # i) vs

    idxRules i = maybe [] (\case
      InstanceV _ _ ->
        mapMaybe (\(i', Edge f mvs) -> do
          rhs <- subst mvs <$> idxApp i
          case idxApp i' of
            Nothing -> Just (Rule [] f rhs)
            Just lhs -> Just (Rule [lhs] f rhs)) (relevantIncoming i)
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
interpolate :: (MonadIO m, Idx idx) => ImplGr idx -> m (Either Model (ImplGr idx))
interpolate g = Z3.solveChc (implGrChc g) >>= \case
  Left m -> return (Left m)
  Right m -> return (Right $ applyModel m g)

-- | Replace the fact at each vertex in the graph by the fact in the model.
applyModel :: Idx idx => Model -> ImplGr idx -> ImplGr idx
applyModel m = G.imapVerts applyVert
  where
    applyVert i = _InstanceV . _2 %~ (\f -> f `mkOr` M.findWithDefault (LBool False) i m')
    m' = M.toList (getModel m)
      & map (traverseOf _1 %%~ interpretName . varName)
      & catMaybes & M.fromList
      where interpretName n = n ^? to uncons . _Just . _2 . written

data Result idx
  = Failed Model
  | Complete (ImplGr idx)
  deriving (Show, Read, Eq)

type SolveState = Map (BaseIdx LinIdx) Integer

type Solve idx m =
  (MonadError (Result idx) m, MonadState SolveState m, MonadIO m)

runSolve :: Monad m => ExceptT e (StateT (Map k a) m) a1 -> m (Either e a1)
runSolve ac = evalStateT (runExceptT ac) M.empty

-- | Repeatedly unwind the program until a counterexample is found or inductive
-- invariants are found.
solve :: MonadIO m => LinIdx -> ImplGr LinIdx -> m (Either Model (ImplGr LinIdx))
solve end g =
  runSolve (loop g) >>= \case
    Left (Failed m) -> return (Left m)
    Left (Complete res) -> return (Right res)
    Right _ -> error "infinite loop terminated successfully?"
  where
    loop gr = loop =<< step end gr

-- | Perform interpolation on the graph (exiting on failure), perform and induction
-- check, and unwind further if required.
step :: Solve LinIdx m => LinIdx -> ImplGr LinIdx -> m (ImplGr LinIdx)
step end g = interpolate g >>= either (throwError . Failed) (\interp -> do
  indM <- inductive end interp
  let isInd = M.keys $ M.filter id indM
  when (M.lookup end indM == Just True) $ throwError $ Complete interp
  unwindAllBackEdges isInd end interp)

-- | Gather all facts known about each instance of the same index together by disjunction.
collectAnswer :: (Ord (BaseIdx idx), Idx idx) => ImplGr idx -> Map (BaseIdx idx) Form
collectAnswer g = execState (G.itravVerts (\i v -> case v of
  InstanceV _ f -> modify (M.insertWith mkOr (i ^. baseIdx) f)
  _ -> return ()) g) M.empty

-- | Unwind the graph on the given backedge and update all instances in the unwinding.
unwind :: Solve idx m => LinIdx -> LinIdx -> Edge -> ImplGr LinIdx -> m (LinIdx, ImplGr LinIdx)
unwind = G.unwind updateInstance (\_ _ -> return) (\_ v -> return $ v & _InstanceV . _2 .~ LBool False)


unwindAllBackEdges :: Solve idx m => [LinIdx] -> LinIdx -> ImplGr LinIdx -> m (ImplGr LinIdx)
unwindAllBackEdges ind end g = do
  let bes = G.backEdges g
  (is, g') <- foldrM (\((i1, i2), e) (is, g') ->
    if any (`elem` ind) (G.idxs (G.reached i1 (G.noBackEdges g')))
    then return (is, g')
    else do (i, g'') <- unwind i1 i2 e g'
            return (i:is, g'')) ([], g) bes
  let g'' = G.ifilterEdges (\i1 i2 e -> ((i1, i2), e) `notElem` bes) g'
  return (compress (mconcat $ map (`G.reached` g'') is) g'')
  where
    compress new g' =
      let compressed = g'
            & G.filterIdxs (\i -> i `notElem` ind || i `elem` G.idxs new)
            & G.ifilterEdges (\i1 i2 e -> ((i1, i2), e) `notElem` G.backEdges g')
            & G.reaches end
      in G.filterIdxs (`elem` G.idxs compressed) g'

-- | Find a fresh instance counter for the given index.
updateInstance :: MonadState SolveState m => LinIdx -> m LinIdx
updateInstance idx = flip (set linInst) idx <$> (at (idx ^. baseIdx) . non 0 <+= 1)
