{-# LANGUAGE TypeFamilies #-}
module Logic.ImplicationGraph.Induction where

import           Control.Lens hiding (Context)
import           Control.Monad.Loops (allM, anyM, orM)
import           Control.Monad.State

import qualified Data.Ord.Graph as G
import           Data.Maybe (fromJust)
import           Data.Map (Map)
import qualified Data.Map as M

import           Logic.Solver.Z3
import           Logic.Formula
import           Logic.ImplicationGraph.Type

-- | Is the full graph inductive?
isInductive :: LblLike lbl => Node' lbl -> ImplGr' lbl -> IO Bool
isInductive start g = evalStateT (ind start) M.empty
  where
    ind n = maybe (computeInd n) return . M.lookup n =<< get

    computeInd n = do
      let node = look n
      b <- case node of
        AndNode      -> allM ind (G.successors n g)
        OrInputNode  -> anyM ind (G.successors n g)
        OrOutputNode -> allM ind (G.successors n g)
        QueryNode _  -> return True
        FoldedNode _ -> return False
        InstanceNode (_, f) -> do
          let ancs = manyOr $ ancestorInstances n
          orM [ return $ f == LBool False
              , liftIO $ entails f ancs
              , allM ind (G.successors n g)
              ]
      modify (M.insert n b)
      return b

    ancestorInstances n =
      let ns = G.ancestors g n
      in concatMap (\n' ->
        if matchNode n n' then
          let anc = look n'
          in case anc of
            InstanceNode (_, f) -> [f]
            _ -> []
        else []) ns

    matchNode (l1, _) (l2, _) = match l1 l2

    idenMatch n1 n2 = case (fst n1, fst n2) of
      ([x], [y]) -> x == y
      ([x, _, x', _], [y, _, y', _]) -> x == y && x' == y'
      _ -> False

    look n = fromJust $ g ^. at n
