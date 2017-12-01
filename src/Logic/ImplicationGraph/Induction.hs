{-# LANGUAGE TypeFamilies #-}
module Logic.ImplicationGraph.Induction where

import           Control.Lens
import           Control.Applicative.Backwards
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Monad.Loops (anyM)

import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G
import qualified Data.Optic.Graph.Extras as G
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Maybe (mapMaybe)
import           Data.Text.Prettyprint.Doc

import           Logic.Formula
import           Logic.Model
import qualified Logic.Solver.Z3 as Z3
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Chc
import           Logic.ImplicationGraph.LTree

import           Prelude hiding (pi)

type InductionState = (Map Idx Bool, Map Loc (Map Idx Form))

-- | Find the vertex labels in the graph which are inductive.
inductive :: MonadIO m => ImplGr -> m (Set Idx)
inductive g = M.keysSet . M.filter id . fst <$> execStateT (ind g (end g)) (M.empty, M.empty)

-- | Decide if the given index is inductive.
ind :: (MonadIO m, MonadState InductionState m) => ImplGr -> Idx -> m Bool
ind g i =
  maybe
    (computeInd g i)        -- compute inductiveness when we don't know the answer
    return                  -- if we memoized the answer, we're done
    . M.lookup i =<< use _1 -- look up the answer from the state

indPred :: (MonadIO m, MonadState InductionState m) => ImplGr -> Idx -> Idx -> m Bool
indPred g i i' =
  if i <= i'        -- if we check the 'predecessor' and it occurs after the current index (back edge)
  then return False -- then it is automatically not inductive
  else ind g i'     -- otherwise, we recurse

computeInd :: (MonadIO m, MonadState InductionState m) => ImplGr -> Idx -> m Bool
computeInd g i =
  (_1 . at i <?=) =<< -- find the answer and update the memoization table
    maybe
      (return False)    -- if there is no vertex, it is trivially not inductive
      (\(Inst loc _ f) -> do
        desc <- descForm loc
        _2 . at loc . non M.empty . at i ?= f
        res <- or <$> sequence       -- this index is inductive if:
          [ return $ f == LBool True --  it is trivially inductive
          , desc `Z3.entails` f      --  a descendant at the same location entails it
          , inductiveByPred g i      --  it's predecessors are inductive
          ]
        _2 . at loc . non M.empty . at i .= Nothing
        return res) (g ^. at i)

inductiveByPred :: (MonadIO m, MonadState InductionState m) => ImplGr -> Idx -> m Bool
inductiveByPred g i = do
  let ies = g ^@.. G.iedgesTo i
  let m = foldr (\(i, e) m ->
        let ts = taggings e in
        foldr (\t -> M.insertWith (++) t (S.toList $ G.start i)) m ts) M.empty ies
  let cats = M.elems m
  or <$> traverse (fmap and . traverse (indPred g i)) cats

-- | Are all predecessors inductive?
allInd :: (MonadIO m, MonadState InductionState m) => ImplGr -> Idx -> [Idx] -> m Bool
allInd g i is = and <$> mapM (indPred g i) is

descForm :: MonadState InductionState m => Loc -> m Form
descForm loc = manyAnd . M.elems . M.findWithDefault M.empty loc <$> use _2

-- | Find the end (query) of the graph
end :: ImplGr -> Idx
end g = head $ filter (\i -> lengthOf (G.edgesFrom i) g == 0) (G.idxs g) -- the query has no outgoing edges

-- | Unwind the graph until a either a counterxample or an inductive
-- solution is found.  Perform a step of the unwinding by
-- 1. interpolating over the current graph
-- 2. checking if the solution is inductive (and terminating if it is)
-- 3. unwinding the graph over all backedges
loop :: MonadIO m => ImplGr -> m (Either Model ImplGr)
loop = runExceptT . loop'
  where
    loop' g = do
      G.display "step" g
      _ <- liftIO getLine
      itp <- interpolate g                              -- interpolate
      indS <- inductive itp                             -- check inductiveness
      if end g `elem` indS                              -- if the query is inductive...
      then return itp                                   -- we're done
      else loop' (unwindAll (backs g) indS (end g) itp) -- otherwise unwind and repeat
    backs = concatMap (\(i, e) -> map ((,) i) (noBr e)) . G.backEdges
