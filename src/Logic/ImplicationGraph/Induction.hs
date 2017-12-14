{-# LANGUAGE TypeFamilies #-}
module Logic.ImplicationGraph.Induction where

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Except
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Maybe (mapMaybe)
import           Data.Text.Prettyprint.Doc
import           Data.Loc
import qualified Data.Optic.Directed.HyperGraph as G
import qualified Data.Optic.Graph.Extras as G

import           Logic.Formula
import qualified Logic.Solver.Z3 as Z3
import           Logic.ImplicationGraph.Accessors
import           Logic.ImplicationGraph.Types
import           Logic.ImplicationGraph.Chc

-- | Find the vertex labels in the graph which are inductive.
inductive :: (Edge f, MonadIO m) => ImplGr f -> m (Set Idx)
inductive g = M.keysSet . M.filter id <$> execStateT (ind g (end g)) M.empty

-- | Decide if the given index is inductive.
ind :: (Edge f, MonadIO m, MonadState (Map Idx Bool) m)
    => ImplGr f -> Idx -> m Bool
ind g i =
  maybe
    (computeInd g i)     -- compute inductiveness when we don't know the answer
    return               -- if we memoized the answer, we're done
    . M.lookup i =<< get -- look up the answer from the state

indPred :: (Edge f, MonadIO m, MonadState (Map Idx Bool) m)
        => ImplGr f -> Idx -> Idx -> m Bool
indPred g i i' =
  if i <= i'        -- if we check the 'predecessor' and it occurs after the current index (back edge)
  then return False -- then it is automatically not inductive
  else ind g i'     -- otherwise, we recurse

computeInd :: (Edge f, MonadIO m, MonadState (Map Idx Bool) m)
           => ImplGr f -> Idx -> m Bool
computeInd g i =
  (at i <?=) =<< -- find the answer and update the memoization table
    maybe
      (return False)    -- if there is no vertex, it is trivially not inductive
      (\(Inst loc _ f) -> do
        let descs = descendantForms g loc i
        or <$> sequence                  -- this index is inductive if:
          [ return $ f == LBool True     --  it is trivially inductive
          , manyAnd descs `Z3.entails` f --  a descendant at the same location entails it
          , inductiveByPred g i          --  it's predecessors are inductive
          ]) (g ^. at i)

inductiveByPred :: (Edge f, MonadIO m, MonadState (Map Idx Bool) m)
                => ImplGr f -> Idx -> m Bool
inductiveByPred g i = do
  let ies = g ^@.. G.iedgesTo i
  let cats = collect (
        concatMap (\(is, e) ->
          map (\i' ->
            fmap (const i') e) (S.toList (G.start is))) ies)
  or <$> traverse (fmap and . traverse (indPred g i)) cats

-- | Are all predecessors inductive?
allInd :: (Edge f, MonadIO m, MonadState (Map Idx Bool) m)
       => ImplGr f -> Idx -> [Idx] -> m Bool
allInd g i is = and <$> mapM (indPred g i) is

-- | Find the formulas of descendants at the same location.
descendantForms :: ImplGr f -> Loc -> Idx -> [Form]
descendantForms g loc i =
  G.descendants i g                      -- look at all descendants
    & S.delete i                         -- an instance cannot entail itself
    & S.toList                           -- convert to a list
    & mapMaybe (\i' -> g ^? ix i')       -- lookup the vertex at each index
    & filter (\v -> v ^. instLoc == loc) -- only consider those at the location in question
    & map _instForm                      -- fetch the formula

-- | Unwind the graph until a either a counterxample or an inductive
-- solution is found.  Perform a step of the unwinding by
-- 1. interpolating over the current graph
-- 2. checking if the solution is inductive (and terminating if it is)
-- 3. unwinding the graph over all backedges
loop :: (MonadIO m, Edge f, Pretty (f Form)) => ImplGr f -> m (Either Model (ImplGr f))
loop =
  runExceptT . loop'
  where
    loop' g = do
      G.display "step" g
      _ <- liftIO getLine
      itp <- interpolate g                              -- interpolate
      indS <- inductive itp                             -- check inductiveness
      if end g `elem` indS                              -- if the query is inductive...
      then return itp                                   -- we're done
      else loop' (unwindAll (backs g) indS (end g) itp) -- otherwise unwind and repeat
    backs = concatMap (\(i, e) -> map ((,) i) (split e)) . G.backEdges
