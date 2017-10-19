{-# LANGUAGE TypeFamilies #-}
module Logic.ImplicationGraph.Induction where

import           Control.Lens hiding (Context)
import           Control.Monad.Loops (allM, anyM, orM)
import           Control.Monad.State

import qualified Data.Ord.Graph as G
import           Data.Maybe (fromJust)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)

import           Logic.Solver.Z3
import           Logic.Formula
import           Logic.ImplicationGraph.Type

-- | Is the full graph inductive?
isInductive :: MonadIO m => LblLike lbl => Node' lbl -> ImplGr' lbl
            -> m (Either (Set (Node' lbl)) (ImplGr' lbl))
isInductive start g = do
  (b, m) <- runStateT (ind start) M.empty
  if b then return (Right g)
  else
    return $ Left $ M.keysSet $ M.filter id m
  where
    ind n = maybe (computeInd n) return . M.lookup n =<< get

    computeInd n = do
      let node = look n
      b <- case node of
        AndNode      -> allInd n
        OrInputNode  -> anyInd n
        OrOutputNode -> allInd n
        QueryNode _  -> return True
        FoldedNode _ -> return False
        InstanceNode (_, f) -> do
          let ancs = manyOr $ ancestorInstances n
          orM [ return $ f == LBool False
              , entails f ancs
              , allInd n
              ]
      modify (M.insert n b)
      return b

    allInd n = and <$> mapM ind (G.successors n g)
    anyInd n = or  <$> mapM ind (G.successors n g)

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
