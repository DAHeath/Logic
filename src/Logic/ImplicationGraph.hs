{-# LANGUAGE TypeFamilies, TemplateHaskell #-}
module Logic.ImplicationGraph where

import           Control.Lens hiding (Context)
import           Control.Monad.State
import           Control.Monad.Except

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
import           Logic.ImplicationGraph.Type
import           Logic.ImplicationGraph.Interpolate
import           Logic.ImplicationGraph.Induction

data Result
  = Failed Model
  | Complete ImplGr
  deriving (Show, Read, Eq)

data SolveState = SolveState
  { _finishedQueries :: [Node]
  , _instanceMap :: Map [Lbl] InstanceId
  } deriving (Show, Read, Eq, Ord, Data)

makeLenses ''SolveState

emptySolveState :: SolveState
emptySolveState = SolveState [] M.empty

solve :: [Int] -> ImplGr -> IO (Either Model ImplGr)
solve dim g = do
  sol <- evalStateT (runExceptT (loop g)) emptySolveState
  case sol of
    Left (Failed m) -> return (Left m)
    Left (Complete res) -> return (Right res)
    Right _ -> error "infinite loop terminated successfully?"
  where
    loop gr = loop =<< step dim gr

step :: [Int] -> ImplGr -> ExceptT Result (StateT SolveState IO) ImplGr
step dim g = do
  let bs = G.backEdges g
  g' <- foldBackedges bs g
  fQuers <- use finishedQueries
  let g'' = G.filterIdxs (`notElem` fQuers) g'
  sol <- liftIO $ interpolate g''
  finishedQueries .= concatMap (\(n, l) -> case l of
    QueryNode _ -> [n]
    _ -> []) (g' ^@.. G.iallVerts)
  case sol of
    Left m -> throwError $ Failed m
    Right g1 -> do
      let start = (map (const 0) dim, 0)
      b <- liftIO $ isInductive start g1
      if b then throwError $ Complete g1
      else do
        let fes = foldedEdges g'
        let g3 = foldr reconnectBackedge g' fes
        foldrM unfold g3 bs

reconnectBackedge :: ((Node, Node), ImplGrEdge) -> ImplGr -> ImplGr
reconnectBackedge ((n1, n2), e) g = case g ^? (at n2 . _Just . _FoldedNode) of
  Nothing -> error "tried to reconnect backedge with non-folded node"
  Just n2' -> G.addEdge n1 n2' e $ G.delIdx n2 g

foldedEdges :: ImplGr -> [((Node, Node), ImplGrEdge)]
foldedEdges g = filter (\((_, n2), _) -> case g ^? (at n2 . _Just . _FoldedNode) of
  Nothing -> False
  Just _ -> True) (g ^@.. G.iallEdges)

-- | Replace all backedges with edges to folded nodes, generating a DAG.
foldBackedges :: MonadState SolveState m => [((Node, Node), ImplGrEdge)] -> ImplGr -> m ImplGr
foldBackedges bs g = do
  let ns = map (snd . fst) bs
  ns' <- mapM latestInstance ns
  let bs' = zipWith (\((n1, _), e) n2 -> ((n1, n2), e)) bs ns'
  let fns = zipWith (\((n1, tar), _) n2 -> (n2, FoldedNode tar)) bs ns'
  if null bs
  then return g
  else return
     $ flip (foldr (\((n1, n2), e) g -> G.addEdge n1 n2 e g)) bs'
     $ flip (foldr (uncurry G.addVert)) fns
     $ G.ifilterEdges (\i1 i2 e -> ((i1, i2), e) `notElem` bs) g

unfold :: MonadState SolveState m => ((Node, Node), e) -> Graph Node e v -> m (Graph Node e v)
unfold ((i1, i2), b) g = do
  let g' = G.reached i2 g
  i2' <- latestInstance i2
  relabelled <- G.travIdxs updateInstance g'
  let merged = G.union g relabelled
  let connected = G.addEdge i1 i2' b merged
  return (G.delEdge i1 i2 connected)

latestInstance :: MonadState SolveState m => Node -> m Node
latestInstance (iden, _) = do
  inst <- M.findWithDefault 0 iden <$> use instanceMap
  return (iden, inst + 1)

updateInstance :: MonadState SolveState m => Node -> m Node
updateInstance (iden, inst) = do
  res <- latestInstance (iden, inst)
  instanceMap . at iden ?= snd res
  return res
