{-# LANGUAGE TypeFamilies #-}
module Logic.ImplicationGraph.Induction where

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Except
import qualified Data.Optic.Directed.HyperGraph as G
import qualified Data.Optic.Graph.Extras as G
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Maybe (mapMaybe)

import           Logic.Formula
import           Logic.Model
import           Logic.Var
import           Logic.Name
import qualified Logic.Solver.Z3 as Z3
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Chc
import           Logic.ImplicationGraph.LTree

-- | Find the vertex labels in the graph which are inductive.
inductive :: (Name n, MonadIO m) => ImplGr n -> m (Set Idx)
inductive g = M.keysSet . M.filter id <$> execStateT (ind g (end g)) M.empty

-- | Decide if the given index is inductive.
ind :: (Name n, MonadIO m, MonadState (Map Idx Bool) m) => ImplGr n -> Idx -> m Bool
ind g i =
  maybe
    (computeInd g i)     -- compute inductiveness when we don't know the answer
    return               -- if we memoized the answer, we're done
    . M.lookup i =<< get -- look up the answer from the state

indPred :: (Name n, MonadIO m, MonadState (Map Idx Bool) m) => ImplGr n -> Idx -> Idx -> m Bool
indPred g i i' =
  if i <= i'        -- if we check the 'predecessor' and it occurs after the current index (back edge)
  then return False -- then it is automatically not inductive
  else ind g i'     -- otherwise, we recurse

computeInd :: (Name n, MonadIO m, MonadState (Map Idx Bool) m) => ImplGr n -> Idx -> m Bool
computeInd g i =
  (at i <?=) =<< -- find the answer and update the memoization table
    maybe
      (return False)    -- if there is no vertex, it is trivially not inductive
      (\(Inst loc _ f) -> do
        let descs = descendantForms g loc i
        dcs <- manyAnd descs `Z3.entails` f
        ip <- inductiveByPred g i
        when (dcs && f /= LBool True) $ liftIO (putStrLn $ "ind by ent: " ++ show i)
        when (ip && f /= LBool True) $ liftIO (putStrLn $ "ind by pred: " ++ show i)
        or <$> sequence                  -- this index is inductive if:
          [ return $ f == LBool True     --  it is trivially inductive
          , return dcs -- manyAnd descs `Z3.entails` f --  a descendant at the same location entails it
          , return ip -- inductiveByPred g i          --  it's predecessors are inductive
          ]) (g ^. at i)

inductiveByPred :: (Name n, MonadIO m, MonadState (Map Idx Bool) m)
                => ImplGr n -> Idx -> m Bool
inductiveByPred g i = do
  let ies = g ^@.. G.iedgesTo i
  let m = foldr (\(i', e) m' ->
        let ts = taggings e in
        foldr (\t -> M.insertWith (++) t (S.toList $ G.start i')) m' ts) M.empty ies
  let cats = M.elems m
  or <$> traverse (fmap and . traverse (indPred g i)) cats

-- | Are all predecessors inductive?
allInd :: (Name n, MonadIO m, MonadState (Map Idx Bool) m)
       => ImplGr n -> Idx -> [Idx] -> m Bool
allInd g i is = and <$> mapM (indPred g i) is

-- | Find the formulas of descendants at the same location.
descendantForms :: ImplGr n -> Loc -> Idx -> [Form n]
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
loop :: (Name n, MonadIO m)
     => ImplGr (Aliasable n) -> m (Either (Model (Aliasable n)) (ImplGr (Aliasable n)))
loop = runExceptT . loop'
  where
    loop' g = do
      -- G.display "step" g
      -- _ <- liftIO getLine
      itp <- interpolate g                              -- interpolate
      indS <- inductive itp                             -- check inductiveness
      if end g `elem` indS                              -- if the query is inductive...
      then return itp                                   -- we're done
      else loop' (unwindAll (backs g) indS (end g) itp) -- otherwise unwind and repeat
    backs = concatMap (\(i, e) -> map ((,) i) (noBr e)) . G.backEdges
