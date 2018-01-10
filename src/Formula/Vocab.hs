{-# LANGUAGE MultiParamTypeClasses, UndecidableInstances #-}
module Formula.Vocab where

import           Control.Lens
import           Control.Monad.State

import           Data.Foldable
import           Data.Data (Data)
import qualified Data.Map as M
import           Data.Map (Map)
import           Data.List.Split

import           Formula.Var

class Monad m => MonadVocab m where
  fresh :: Var -> m Var
  table :: m (Var -> Var)

newtype VocabT m a = Vocab { getVocab :: StateT (Map String Int) m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadTrans)

instance MonadState s m => MonadState s (VocabT m) where
  state = lift . state

instance Monad m => MonadVocab (VocabT m) where
  fresh v = Vocab $ do
    let n = unaliasedVarName v
    m <- get
    case M.lookup n m of
      Nothing -> do
        put (M.insert n 0 m)
        return (v & varName .~ (n ++ "\\0"))
      Just i -> do
        put (M.insert n (i+1) m)
        return (v & varName .~ (n ++ ("\\" ++ show (i+1))))

  table = Vocab $ do
    m <- get
    return (\v -> case M.lookup (unaliasedVarName v) m of
      Nothing -> v
      Just i -> v & varName .~ (unaliasedVarName v ++ "\\" ++ show i))

instance MonadVocab m => MonadVocab (StateT s m) where
  fresh = lift . fresh
  table = lift table

type Vocab a = VocabT Identity a

runVocab :: Vocab a -> a
runVocab (Vocab a) = runIdentity (evalStateT a M.empty)

unaliasedVarName :: Var -> String
unaliasedVarName = unaliasName . view varName

unaliasName :: String -> String
unaliasName n = case splitOn "\\" n of
  [x,_] -> x
  [x] -> x
  _ -> error "invalid variable name has more than 1 instance of '\\'"

unaliasedVar :: Var -> Var
unaliasedVar v = v & varName %~ unaliasName

aliasCount :: Var -> Int
aliasCount = read . last . splitOn "\\" . view varName

-- | Replace the variables in the structure with the following constraints:
-- Nothing from the list of taken variables can appear on the right hand side unless it is
-- in the list of substitutes.
-- The variables on the left of the list of substitutes will be replaced by the corresponding
-- variable on the right.
freshen :: (Data a, MonadVocab m) => Map Var Var -> a -> m a
freshen tab x = subst <$> aliasMap <*> pure x
  where
    aliasMap = foldrM addAlias tab (varSet x)
    addAlias v m =
      if v `elem` M.keys tab
      then pure m
      else do
        v' <- fresh v
        pure $ M.insert v v' m
