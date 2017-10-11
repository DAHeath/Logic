{-# LANGUAGE TypeFamilies #-}
module Logic.ImplicationGraph.Induction where

import           Control.Lens hiding (Context)
import           Control.Monad.Loops (allM, anyM)
import           Control.Monad.Extra (whenM)
import           Control.Monad.State

import           Data.Graph.Inductive.Graph hiding ((&))
import           Data.Graph.Inductive.Extras hiding (backEdges)
import           Data.Graph.Inductive.Query.DFS (topsort)
import           Data.Maybe (fromJust)

import           Logic.Solver.Z3
import           Logic.Formula
import           Logic.ImplicationGraph.Type

-- | Is the full graph inductive?
isInductive :: ImplGr -> IO (Bool, ImplGr)
isInductive g = do
  let ord = topsort g
  runStateT (do
    mapM_ ind (reverse ord)
    isNodeInd 0) g
  where
    ind :: Node -> StateT ImplGr IO ()
    ind n = do
      node <- look n
      case node of
        AndNode _ -> indSucc allM _AndNode n
        OrInputNode _ -> indSucc anyM _OrInputNode n
        OrOutputNode _ -> indSucc allM _OrOutputNode n
        InstanceNode i -> do
          indSucc allM (_InstanceNode . inductive) n
          when (i ^. formula == LBool False)
            (instanceInductive n .= InductiveFalse)
          ancs <- ancestorInstances n (i ^. identity)
          void $ anyM (covers n i) ancs
        QueryNode _ -> return ()
        FoldedNode _ -> return ()

    indSucc f l n =
      whenM (f isNodeInd (suc g n)) (at n . _Just . l .= InductiveSucc)

    instanceInductive n = at n . _Just . _InstanceNode . inductive

    covers n i (n', f) = do
      b <- liftIO $ entails (i ^. formula) f
      when b (instanceInductive n .= InductiveBy n')
      return b

    ancestorInstances :: Node -> [Lbl] -> StateT ImplGr IO [(Node, Form)]
    ancestorInstances n iden = do
      ns <- ancestors <$> get <*> pure n
      concat <$> mapM (\n' -> do
        anc <- look n'
        case anc of
          InstanceNode i ->
            if i ^. identity == iden
            then return [(n', i ^. formula)]
            else return []
          _ -> return []) ns

    look :: Node -> StateT ImplGr IO ImplGrNode
    look n = fromJust <$> use (at n)

    isNodeInd :: Node -> StateT ImplGr IO Bool
    isNodeInd n = isLblInd <$> look n

-- | Check if the node is inductive.
isLblInd :: ImplGrNode -> Bool
isLblInd = \case
  AndNode i -> isInd i
  OrInputNode i -> isInd i
  OrOutputNode i -> isInd i
  InstanceNode i -> isInd (i ^. inductive)
  QueryNode _ -> True
  FoldedNode _ -> False

-- | Check if the inductive label indicates it is inductive.
isInd :: Inductive -> Bool
isInd = \case
  NotInductive       -> False
  UnknownIfInductive -> False
  InductiveSucc      -> True
  InductiveFalse     -> True
  InductiveBy _      -> True
