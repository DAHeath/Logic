{-# LANGUAGE TypeFamilies, TemplateHaskell, ConstraintKinds #-}
module Logic.ImplicationGraph.Solve where

import           Control.Lens hiding (Context)
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Arrow

import           Data.Data
import           Data.Ord.Graph (Graph)
import qualified Data.Ord.Graph as G
import qualified Data.Ord.Graph.Extras as G
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (mapMaybe)
import           Data.Foldable (foldrM)

import           Logic.Model
import           Logic.Formula
import           Logic.ImplicationGraph.Type
import           Logic.ImplicationGraph.Interpolate
import           Logic.ImplicationGraph.Induction

data Result' lbl
  = Failed Model
  | Complete (ImplGr' lbl)
  deriving (Show, Read, Eq)

type Result = Result' Lbl

data SolveState' lbl = SolveState
  { _finishedQueries :: [Node' lbl]
  , _instanceMap :: Map lbl InstanceId
  , _andNode :: Node' lbl
  , _orInputNode :: Node' lbl
  , _orOutputNode :: Node' lbl
  , _foldedNode :: Node' lbl
  } deriving (Show, Read, Eq, Ord, Data)

makeLenses ''SolveState'

mapSolveState :: Ord b => (a -> b) -> SolveState' a -> SolveState' b
mapSolveState f (SolveState qs m andN orInputN orOutputN foldN)
  = SolveState (map (first f) qs)
               (M.mapKeys f m)
               (first f andN)
               (first f orInputN)
               (first f orOutputN)
               (first f foldN)

type SolveState = SolveState' Lbl
type Solve lbl m =
  (MonadError (Result' lbl) m, MonadState (SolveState' lbl) m, MonadIO m)

emptySolveState :: ImplGr -> SolveState
emptySolveState g =
  let andNode = S.findMax (G.idxSet g) & _1 +~ 1
      orInputNode = andNode & _1 +~ 1
      orOutputNode = orInputNode & _1 +~ 1
      foldedNode = orOutputNode & _1 +~ 1
  in SolveState [] M.empty andNode orInputNode orOutputNode foldedNode

solve :: MonadIO m => [Int] -> ImplGr -> m (Either Model ImplGr)
solve dim g = do
  sol <- evalStateT (runExceptT (loop g)) (emptySolveState g)
  case sol of
    Left (Failed m) -> return (Left m)
    Left (Complete res) -> return (Right res)
    Right _ -> error "infinite loop terminated successfully?"
  where
    loop gr = loop =<< step (0, 0) gr

backEdges' :: LblLike lbl => ImplGr' lbl -> [((Node' lbl, Node' lbl), ImplGrEdge)]
backEdges' = G.backEdges . withoutModNodes

withoutModNodes :: LblLike lbl => ImplGr' lbl -> ImplGr' lbl
withoutModNodes =
  G.filterVerts
    (\v -> not (has _AndNode v || has _OrInputNode v || has _OrOutputNode v || has _FoldedNode v))

step :: (LblLike lbl, Solve lbl m) => Node' lbl -> ImplGr' lbl -> m (ImplGr' lbl)
step start g = do
  let bs = G.backEdges g
  g' <- foldBackedges bs g
  fQuers <- use finishedQueries
  let g'' = G.filterIdxs (`notElem` fQuers) g'
  sol <- interpolate g''
  finishedQueries .= concatMap (\(n, l) -> case l of
    QueryNode _ -> [n]
    _ -> []) (g' ^@.. G.iallVerts)
  case sol of
    Left m -> throwError $ Failed m
    Right g1 -> do
      ind <- isInductive start g1
      case ind of
        Right done -> throwError $ Complete done
        Left indS -> do
          let fes = foldedEdges $ G.filterIdxs (`notElem` indS) g'
          let g3 = foldr reconnectBackedge g' fes
          foldrM unfold g3 bs

collectAnswer :: (Ord (Base lbl), LblLike lbl) => ImplGr' lbl -> Map (Base lbl) Form
collectAnswer g =
  execState (G.itravVerts (\k v -> case v of
    InstanceNode i -> modify (M.insertWith mkOr (toBase (fst k)) (snd i))
    _ -> return ()) g) M.empty

reconnectBackedge :: LblLike lbl => ((Node' lbl, Node' lbl), ImplGrEdge) -> ImplGr' lbl -> ImplGr' lbl
reconnectBackedge ((n1, n2), e) g = case g ^? (at n2 . _Just . _FoldedNode) of
  Nothing -> error "tried to reconnect backedge with non-folded node"
  Just n2' -> G.addEdge n1 n2' e $ G.delIdx n2 g

foldedEdges :: LblLike lbl => ImplGr' lbl -> [((Node' lbl, Node' lbl), ImplGrEdge)]
foldedEdges g = filter (\((_, n2), _) -> case g ^? (at n2 . _Just . _FoldedNode) of
  Nothing -> False
  Just _ -> True) (g ^@.. G.iallEdges)

-- | Replace all backedges with edges to folded nodes, generating a DAG.
foldBackedges :: (LblLike lbl, MonadState (SolveState' lbl) m)
              => [((Node' lbl, Node' lbl), ImplGrEdge)] -> ImplGr' lbl -> m (ImplGr' lbl)
foldBackedges bs g = do
  let ns = map (snd . fst) bs
  ns' <- mapM (const newFoldedNode) ns
  let bs' = zipWith (\((n1, _), e) n2 -> ((n1, n2), e)) bs ns'
  let fns = zipWith (\((n1, tar), _) n2 -> (n2, FoldedNode tar)) bs ns'
  if null bs
  then return g
  else return
     $ flip (foldr (\((n1, n2), e) g -> G.addEdge n1 n2 e g)) bs'
     $ flip (foldr (uncurry G.addVert)) fns
     $ G.ifilterEdges (\i1 i2 e -> ((i1, i2), e) `notElem` bs) g

unfold :: (LblLike lbl, MonadState (SolveState' lbl) m)
       => ((Node' lbl, Node' lbl), e) -> Graph (Node' lbl) e v -> m (Graph (Node' lbl) e v)
unfold ((i1, i2), b) g = do
  let g' = G.reached i2 g
  i2' <- latestInstance i2
  relabelled <- G.travIdxs updateInstance g'
  let merged = G.union g relabelled
  let connected = G.addEdge i1 i2' b merged
  return (G.delEdge i1 i2 connected)

newAndNode :: (LblLike lbl, MonadState (SolveState' lbl) m) => m (Node' lbl)
newAndNode = use andNode >>= updateInstance

newOrInputNode :: (LblLike lbl, MonadState (SolveState' lbl) m) => m (Node' lbl)
newOrInputNode = use orInputNode >>= updateInstance

newOrOutputNode :: (LblLike lbl, MonadState (SolveState' lbl) m) => m (Node' lbl)
newOrOutputNode = use orOutputNode >>= updateInstance

newFoldedNode :: (LblLike lbl, MonadState (SolveState' lbl) m) => m (Node' lbl)
newFoldedNode = use foldedNode >>= updateInstance

addAndNode :: (LblLike lbl, MonadState (SolveState' lbl) m)
           => [Node' lbl] -> Node' lbl -> ImplGrEdge -> ImplGr' lbl -> m (ImplGr' lbl)
addAndNode srcs tgt e g = do
  a <- newAndNode
  return $
    foldr (\n -> G.addEdge n a (ImplGrEdge (LBool True) M.empty))
      (G.addEdge a tgt e $ G.addVert a AndNode g) srcs

latestInstance :: (LblLike lbl, MonadState (SolveState' lbl) m) => Node' lbl -> m (Node' lbl)
latestInstance (iden, _) = do
  inst <- M.findWithDefault 0 iden <$> use instanceMap
  return (iden, inst + 1)

updateInstance :: (LblLike lbl, MonadState (SolveState' lbl) m) => Node' lbl -> m (Node' lbl)
updateInstance (iden, inst) = do
  res <- latestInstance (iden, inst)
  instanceMap . at iden ?= snd res
  return res
