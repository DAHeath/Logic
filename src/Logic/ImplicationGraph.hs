{-# LANGUAGE DeriveDataTypeable, TypeFamilies, TemplateHaskell, ConstraintKinds #-}
module Logic.ImplicationGraph where

import           Control.Lens
import           Control.Arrow ((***))
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Monad.Loops (anyM)

import           Data.Data
import           Data.Optic.Graph (Graph)
import qualified Data.Optic.Graph as G
import qualified Data.Optic.Graph.Extras as G
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (catMaybes)
import           Data.List.Split (splitOn)
import           Data.List (find)
import           Data.Foldable (foldrM)
import           Data.Text.Prettyprint.Doc

import           Logic.Formula
import           Logic.Model
import           Logic.Var
import qualified Logic.Solver.Z3 as Z3

import           Text.Read (readMaybe)

data Vert
  = InstanceV [Var] Form
  | QueryV Form
  deriving (Show, Read, Eq, Ord, Data)
makePrisms ''Vert

data Edge = Edge
  { _edgeForm :: Form
  , _edgeMap :: Map Var Var
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Edge

data Idx = Idx { _idxIden :: Integer, _idxInst :: Integer }
  deriving (Show, Read, Eq, Data)
makeLenses ''Idx

instance Ord Idx where
  compare (Idx iden1 inst1) (Idx iden2 inst2) =
    case compare inst1 inst2 of
      LT -> GT
      GT -> LT
      EQ -> compare iden1 iden2

freshIdx :: Integer -> Idx
freshIdx i = Idx i 0

type HyperEdges = Map Integer [(Integer, Integer)]

data ImplGr edge = ImplGr
  { _implGr :: Graph Idx edge Vert
  , _entrance :: Idx
  , _exit :: Idx
  , _hyperEdges :: HyperEdges
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''ImplGr

fromGraph :: AsInteger idx => Graph idx edge Vert -> HyperEdges -> Maybe (ImplGr edge)
fromGraph g hs = ImplGr g' theEntry <$> theQuery <*> pure hs
  where
    g' = G.mapIdxs (freshIdx . asInteger) g
    theQuery = fst <$> (g' ^@? G.iallVerts . _QueryV)
    theEntry = minimum $ G.idxs g'

type instance Index (ImplGr e) = Idx
type instance IxValue (ImplGr e) = Vert
instance Ixed (ImplGr e)
instance At (ImplGr e) where at i = implGr . at i

emptyInst :: [Var] -> Vert
emptyInst vs = InstanceV vs (LBool False)

instance Pretty Edge where
  pretty (Edge f m) = pretty f <+> pretty (M.toList m)

instance Pretty Vert where
  pretty = \case
    InstanceV vs f -> pretty vs <+> pretty f
    QueryV f -> pretty f

class AsInteger a where
  asInteger :: a -> Integer

instance AsInteger Integer where
  asInteger = id

match :: Idx -> Idx -> Bool
match x y = x ^. idxIden == y ^. idxIden

written :: Prism' String Idx
written = prism' toWritten fromWritten
  where
    toWritten (Idx iden i) = show iden ++ "_" ++ show i
    fromWritten s = case splitOn "_" s of
        [iden, i] -> Idx <$> readMaybe iden <*> readMaybe i
        _ -> Nothing

instance Pretty Idx where
  pretty (Idx iden i) = pretty iden <+> pretty i

-- | Augment the fact at each vertex in the graph by the fact in the model.
applyModel :: Model -> ImplGr Edge -> ImplGr Edge
applyModel m = implGr %~ G.imapVerts applyVert
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
  | Complete (ImplGr e)
  deriving (Show, Read, Eq)

type SolveState = Map Integer Integer

type Solve e m =
  (MonadError (Result e) m, MonadState SolveState m, MonadIO m)

runSolve :: Monad m => ExceptT e (StateT (Map k a) m) a1 -> m (Either e a1)
runSolve ac = evalStateT (runExceptT ac) M.empty

-- | Gather all facts known about each instance of the same index together by disjunction.
collectAnswer :: MonadIO m => ImplGr Edge -> m (Map Integer Form)
collectAnswer g = traverse Z3.superSimplify $ execState (G.itravVerts (\i v -> case v of
  InstanceV _ f ->
    if f == LBool True then return ()
    else modify (M.insertWith mkOr (i ^. idxIden) f)
  _ -> return ()) (g ^. implGr)) M.empty

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
