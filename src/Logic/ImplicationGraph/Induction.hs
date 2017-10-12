{-# LANGUAGE TypeFamilies #-}
module Logic.ImplicationGraph.Induction where

import           Control.Lens hiding (Context)
import           Control.Monad.Loops (allM, anyM, orM)
import           Control.Monad.State

import           Data.Graph.Inductive.Graph hiding ((&))
import           Data.Graph.Inductive.Extras hiding (backEdges)
import           Data.Maybe (fromJust)
import           Data.IntMap (IntMap)
import qualified Data.IntMap as M

import           Logic.Solver.Z3
import           Logic.Formula
import           Logic.ImplicationGraph.Type

-- | Is the full graph inductive?
isInductive :: ImplGr -> IO Bool
isInductive g = evalStateT (ind 0) M.empty
  where
    ind :: Node -> StateT (IntMap Bool) IO Bool
    ind n = maybe (computeInd n) return . M.lookup n =<< get

    computeInd :: Node -> StateT (IntMap Bool) IO Bool
    computeInd n = do
      let node = look n
      b <- case node of
        AndNode      -> allM ind (suc g n)
        OrInputNode  -> anyM ind (suc g n)
        OrOutputNode -> allM ind (suc g n)
        QueryNode _  -> return True
        FoldedNode _ -> return False
        InstanceNode i -> do
          let ancs = manyOr $ ancestorInstances n (i ^. identity)
          orM [ return $ i ^. formula == LBool False
              , liftIO $ entails (i ^. formula) ancs
              , allM ind (suc g n)
              ]
      modify (M.insert n b)
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
