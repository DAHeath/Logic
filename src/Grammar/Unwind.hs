module Grammar.Unwind where

import           Control.Lens
import           Control.Monad
import           Control.Monad.State

import qualified Data.Map as M
import qualified Data.Set as S
import           Data.List (partition)

import           Grammar.Grammar

 -- | Find the corresponding non-recursive grammar from the given start symbol.
 -- That is, remove all productions which contain nonterminals which have already
 -- been seen.
nonrecursive :: Grammar -> Grammar
nonrecursive g =
  let g' = killLoop g in
  if g' == g then g'
  else nonrecursive g'
  where
    killLoop g = let (_, old, _) = unwind' [] g in g & grammarRules .~ old

-- | Find the first recursive invocation in the grammar along each branch and unwind it.
-- That is, follow the rules until a nonterminal symbol appears which has already been
-- seen. Create new copies of all the rules succeeding this one with new symbols.
unwind :: (Clones, Grammar) -> (Clones, Grammar)
unwind (clones, g) = let (clones', old, new) = unwind' clones g in (clones', g & grammarRules .~ (old ++ new))

unwind' :: Clones -> Grammar -> (Clones, [Rule], [Rule])
unwind' clones (Grammar start rs) =
  let (clones', toAdd, toDelete, _, _) =
         execState (recNT [start] start) (clones, [], [], S.empty, highestSym) in
  (clones', filter (`notElem` toDelete) rs, toAdd)
  where
    highestSym = maximum (map (view (ruleLHS . productionSymbol)) rs)
    recNT seen nt = do
      visited <- use _4
      unless (nt `elem` visited) $ do
        _4 %= S.insert nt
        let rs' = rulesFor nt rs
        let (rec, nonrec) =
              partition (\r -> any (`elem` (nt:seen)) (r ^.. ruleRHS . traverse . productionSymbol)) rs'
        case rec of
          (r:_) -> expand (nt : seen) r
          [] -> mapM_ (recRule (nt : seen)) nonrec

    expand seen (Rule cats lhs body rhs) = do
      _3 %= (Rule cats lhs body rhs:)
      rhs' <- evalStateT (mapM (cloneNT seen) rhs) M.empty
      _2 %= (Rule cats lhs body rhs':)

    recRule seen r = mapM_ (recNT seen . view productionSymbol) (r ^. ruleRHS)

    cloneNT seen nt = do
      m <- get
      case M.lookup (nt ^. productionSymbol) m of
        Just i -> pure (nt & productionSymbol .~ i)
        Nothing -> do
          i <- newInst (nt ^. productionSymbol )
          mapM_ (cloneRule seen) (rulesFor (nt ^. productionSymbol) rs)
          pure (nt & productionSymbol .~ i)

    cloneRule seen (Rule cats lhs body rhs) = do
      m <- get
      let lhs' = lhs & productionSymbol .~ m M.! (lhs ^. productionSymbol)
      rhs' <- mapM (cloneNT ((lhs ^. productionSymbol) : seen)) rhs
      lift (_2 %= (Rule cats lhs' body rhs':))

    newInst i = do
      m <- get
      j <- lift (use _5)
      put (M.insert i (j+1) m)
      lift (_5 += 1)
      lift (addClone i (j+1))
      return (j+1)

    addClone i j = _1 %= clone i j
