module Grammar.Unwind where

import           Control.Lens
import           Control.Monad.State

import           Data.Data.Lens
import qualified Data.Map as M

import           Grammar.Grammar

 -- | Find the corresponding non-recursive grammar from the given start symbol.
 -- That is, remove all productions which contain nonterminals which have already
 -- been seen.
nonrecursive :: Symbol -> Grammar -> Grammar
nonrecursive start g = fst $ unwind' start g

unwind :: Symbol -> Grammar -> Grammar
unwind start g = let (old, new) = unwind' start g in old ++ new

unwind' :: Symbol -> Grammar -> (Grammar, Grammar)
unwind' start g =
  let (toAdd, toDelete) = execState (recNT [start] start) ([], []) in
  (filter (`notElem` toDelete) g, toAdd)
  where
    highestInst = maximum (map controlSymbol (g ^. biplate))

    recNT seen nt = mapM_ (recRule seen) (rulesFor nt g)
    recRule seen (Rule lhs rhs) =
      if any (`elem` seen) (map controlSymbol $ rhsProductions rhs)
      then do
        _2 %= (Rule lhs rhs:)
        rhsPs' <- evalStateT
          (mapM (cloneNT (controlSymbol lhs : seen)) (rhsProductions rhs)) (M.empty, highestInst)
        _1 %= (Rule lhs (RHS (rhsConstraint rhs) rhsPs'):)
      else
        mapM_ (recNT (controlSymbol lhs:seen) . controlSymbol) (rhsProductions rhs)

    cloneNT seen nt = do
      (m, _) <- get
      case M.lookup (controlSymbol nt) m of
        Just i -> pure nt { controlSymbol = i }
        Nothing -> do
          i <- newInst (controlSymbol nt)
          mapM_ (cloneRule seen) (rulesFor (controlSymbol nt) g)
          pure (nt { controlSymbol = i })

    cloneRule seen (Rule lhs rhs) = do
      (m, _) <- get
      let lhs' = lhs { controlSymbol = m M.! controlSymbol lhs }
      rhsPs' <- mapM (cloneNT (controlSymbol lhs : seen)) (rhsProductions rhs)
      lift (_1 %= (Rule lhs' (RHS (rhsConstraint rhs) rhsPs'):))

    newInst i = do
      (m, j) <- get
      put (M.insert i (j+1) m, j+1)
      return (j+1)
