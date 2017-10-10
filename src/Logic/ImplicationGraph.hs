{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
module Logic.ImplicationGraph where

import           Control.Lens hiding (Context)
import           Control.Monad.State
import           Control.Monad.Except

import           Data.Graph.Inductive.Graph hiding ((&))
import           Data.Graph.Inductive.Basic
import           Data.Graph.Inductive.Extras hiding (backEdges)
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

data Result
  = Failed Model
  | Complete ImplGr
  deriving (Show, Read, Eq)

solve :: [Int] -> ImplGr -> IO (Either Model ImplGr)
solve dim g = do
  let g' = foldBackedges bs g
  sol <- evalStateT (runExceptT (loop g')) M.empty
  case sol of
    Left (Failed m) -> return (Left m)
    Left (Complete res) -> return (Right res)
    Right _ -> error "infinite loop terminated successfully?"
  where
    bs = backEdges dim g
    loop gr = loop =<< step bs gr

step :: [LEdge ImplGrEdge] -> ImplGr
     -> ExceptT Result (StateT (Map [Lbl] InstanceId) IO) ImplGr
step bs g = do
  sol <- liftIO $ interpolate g
  case sol of
    Left m -> throwError $ Failed m
    Right g1 -> do
      (b, g2) <- liftIO $ isInductive g1
      if b then throwError $ Complete g2
      else do
        let fes = foldedEdges g2
        let g3 = foldr reconnectBackedge g2 fes
        let g4 = foldr unfold g3 bs
        g5 <- relabelNewInstances g3 g4
        return (foldBackedges bs g5)

  where
    relabelNewInstances g1 g2 =
      let ns = [order g1.. order g2-1]
      in foldrM relabelNode g2 ns

    relabelNode n g' = g' & at n . _Just . _InstanceNode %%~ relabelInstance

    relabelInstance i = do
      m <- get
      let inst = M.findWithDefault 0 (i ^. identity) m
      let m' = M.insert (i ^. identity) (inst + 1) m
      put m'
      return (i & instanceId .~ (inst + 1))

reconnectBackedge :: LEdge ImplGrEdge -> ImplGr -> ImplGr
reconnectBackedge (n1, n2, e) g = case g ^? (at n2 . _Just . _FoldedNode) of
  Nothing -> error "tried to reconnect backedge with non-folded node"
  Just n2' -> insEdge (n1, n2', e) $ delNode n2 g

foldedEdges :: ImplGr -> [LEdge ImplGrEdge]
foldedEdges g = filter (\(_, n2, _) -> case g ^? (at n2 . _Just . _FoldedNode) of
  Nothing -> False
  Just _ -> True) (labEdges g)

-- | Replace all backedges with edges to folded nodes, generating a DAG.
foldBackedges :: [LEdge ImplGrEdge] -> ImplGr -> ImplGr
foldBackedges bs g =
  let ns = newNodes (length bs) g
      bs' = zipWith (\(n1, _, e) n2 -> (n1, n2, e)) bs ns
      ns' = zip ns (map (\(n1, _, _) -> FoldedNode n1) bs)
  in if null bs then g
     else flip (foldr insEdge) bs'
        $ flip (foldr insNode) ns'
        $ efilter (`notElem` bs) g

-- | Backedges are those edges which go from one instance node to another and
-- the target has a lower identity than the source.
backEdges :: [Int] -> ImplGr -> [LEdge ImplGrEdge]
backEdges dims g = S.toList $ ufold (\c s -> s `S.union` ctxSet c) S.empty g
  where
    ctxSet :: Context ImplGrNode ImplGrEdge -> Set (LEdge ImplGrEdge)
    ctxSet (bef, n, here, aft) =
      let befSets = mapMaybe (\(e, n') -> do
                                l <- lab g n'
                                return (backEdgeSet e (n', l) (n, here))) bef
          aftSets = mapMaybe (\(e, n') -> do
                                l <- lab g n'
                                return (backEdgeSet e (n, here) (n', l))) aft
      in S.unions (befSets ++ aftSets)

    backEdgeSet :: ImplGrEdge
                -> LNode ImplGrNode
                -> LNode ImplGrNode
                -> Set (LEdge ImplGrEdge)
    backEdgeSet e (n1, l1) (n2, l2) = case (l1, l2) of
      (InstanceNode l1', InstanceNode l2') ->
        if (l2' ^. identity) `leq` (l1' ^. identity)
        then S.singleton (n1, n2, e)
        else S.empty
      _ -> S.empty

    leq :: [Lbl] -> [Lbl] -> Bool
    leq x y = loc x <= loc y

    loc :: [Lbl] -> Int
    loc = sum . zipWith dimension [0..]
      where
        dimension dim i = i * product (take dim dims)
