module Grammar.Unwind where

import           Control.Lens
import           Control.Monad
import           Control.Monad.State

import qualified Data.Map as M
import qualified Data.Set as S

import           Grammar.Grammar

 -- | Find the corresponding non-recursive grammar from the given start symbol.
 -- That is, remove all productions which contain nonterminals which have already
 -- been seen.
nonrecursive :: Grammar -> Grammar
nonrecursive g = let (_, old, _) = unwind' [] g in g & grammarRules .~ old

-- | Find the first recursive invocation in the grammar along each branch and unwind it.
-- That is, follow the rules until a nonterminal symbol appears which has already been
-- seen. Create new copies of all the rules succeeding this one with new symbols.
unwind :: (Clones, Grammar) -> (Clones, Grammar)
unwind (clones, g) = let (clones', old, new) = unwind' clones g in (clones', g & grammarRules .~ (old ++ new))

unwind' :: Clones -> Grammar -> (Clones, [Rule], [Rule])
unwind' clones (Grammar start rs) =
  let (clones', toAdd, toDelete, _) = execState (recNT [start] start) (clones, [], [], S.empty) in
  (clones', filter (`notElem` toDelete) rs, toAdd)
  where
    highestSym = maximum (map (view (ruleLHS . productionSymbol)) rs)
    recNT seen nt = do
      visited <- use _4
      unless (nt `elem` visited) $ do
        _4 %= S.insert nt
        mapM_ (recRule (nt : seen)) (rulesFor nt rs)

    recRule seen (Rule lhs body rhs) =
      if any (`elem` seen) (map (view productionSymbol) rhs)
      then do
        _3 %= (Rule lhs body rhs:)
        rhs' <- evalStateT
          (mapM (cloneNT seen) rhs) (M.empty, highestSym)
        _2 %= (Rule lhs body rhs':)
      else
        mapM_ (recNT seen . view productionSymbol) rhs

    cloneNT seen nt = do
      (m, _) <- get
      case M.lookup (nt ^. productionSymbol) m of
        Just i -> pure (nt & productionSymbol .~ i)
        Nothing -> do
          i <- newInst (nt ^. productionSymbol )
          mapM_ (cloneRule seen) (rulesFor (nt ^. productionSymbol) rs)
          pure (nt & productionSymbol .~ i)

    cloneRule seen (Rule lhs body rhs) = do
      (m, _) <- get
      let lhs' = lhs & productionSymbol .~ m M.! (lhs ^. productionSymbol)
      rhs' <- mapM (cloneNT ((lhs ^. productionSymbol) : seen)) rhs
      lift (_2 %= (Rule lhs' body rhs':))

    newInst i = do
      (m, j) <- get
      put (M.insert i (j+1) m, j+1)
      lift (addClone i (j+1))
      return (j+1)

    addClone i j = _1 %= clone i j
