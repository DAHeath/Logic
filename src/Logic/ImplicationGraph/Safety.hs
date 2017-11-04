module Logic.ImplicationGraph.Safety where

import           Control.Monad.State
import           Control.Monad.Except

import qualified Data.Optic.Graph as G
import qualified Data.Map as M
import           Data.Map (Map)

import           Logic.Model
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Induction

inductive :: MonadIO m => Idx -> ImplGr Idx -> m (Map Idx Bool)
inductive = inductive' pred
  where
    pred g i = (: []) <$> allInd pred g i (G.predecessors i g)

-- | Repeatedly unwind the program until a counterexample is found or inductive
-- invariants are found.
solve :: MonadIO m => Integer -> ImplGr Integer -> m (Either Model (ImplGr Idx))
solve end g =
  let g' = G.mapIdxs firstInst g in
  runSolve (loop g') >>= \case
    Left (Failed m) -> return (Left m)
    Left (Complete res) -> return (Right res)
    Right _ -> error "infinite loop terminated successfully?"
  where
    loop gr = loop =<< step (firstInst end) gr

-- | Perform interpolation on the graph (exiting on failure), perform and induction
-- check, and unwind further if required.
step :: Solve Edge m => Idx -> ImplGr Idx -> m (ImplGr Idx)
step end g = interpolate g >>= either (throwError . Failed) (\interp -> do
  indM <- inductive end interp
  let isInd = M.keys $ M.filter id indM
  when (M.lookup end indM == Just True) $ throwError $ Complete interp
  unwindAll (G.backEdges g) isInd end interp)

