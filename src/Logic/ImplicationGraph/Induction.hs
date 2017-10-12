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
import           Data.Map (Map)
import qualified Data.Map as M

import           Logic.Solver.Z3
import           Logic.Formula
import           Logic.ImplicationGraph.Type

-- | Is the full graph inductive?
isInductive :: ImplGr -> IO Bool
isInductive g = evalStateT (ind 0) M.empty
  where
    ind :: Node -> StateT (Map Node Inductive) IO Bool
    ind n = do
      i <- M.lookup n <$> get
      case i of
        Just i' -> return $ isInd i'
        Nothing -> computeInd n

    computeInd :: Node -> StateT (Map Node Inductive) IO Bool
    computeInd n =
      let node = look n
      in case node of
        AndNode -> indSucc allM n
        OrInputNode -> indSucc anyM n
        OrOutputNode -> indSucc allM n
        InstanceNode i -> do
          let ancs = manyOr $ ancestorInstances n (i ^. identity)
          b <- covers n i ancs
          if b then return True
          else if i ^. formula == LBool False
            then do
              modify (M.insert n InductiveFalse)
              return False
            else
              indSucc allM n
        QueryNode _ -> return True
        FoldedNode _ -> return False

    indSucc f n = do
      b <- f ind (suc g n)
      if b then do
        modify (M.insert n InductiveSucc)
        return True
      else return False

    covers n i f = do
      b <- liftIO $ entails (i ^. formula) f
      when b (modify (M.insert n InductiveCover))
      return b

    ancestorInstances :: Node -> [Lbl] -> [Form]
    ancestorInstances n iden =
      let ns = ancestors g n
      in concatMap (\n' ->
        let anc = look n'
        in case anc of
          InstanceNode i -> [i ^. formula | i ^. identity == iden]
          _ -> []) ns

    look :: Node -> ImplGrNode
    look n = fromJust $ g ^. at n

-- | Check if the inductive label indicates it is inductive.
isInd :: Inductive -> Bool
isInd = \case
  NotInductive   -> False
  InductiveSucc  -> True
  InductiveFalse -> True
  InductiveCover -> True
