module Grammar.Inductive where

import           Control.Lens
import           Control.Monad.State

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Maybe (fromMaybe)

import           Logic.Formula hiding (Rule)
import qualified Logic.Solver.Z3 as Z3
import           Grammar.Grammar

isInductive :: Clones -> Grammar -> Map Symbol Form -> IO Bool
isInductive clones g m = evalStateT (ind S.empty (g ^. grammarStart)) M.empty
  where
    descs sym =
      let cs = fromMaybe S.empty (cloneFor sym clones)
          ds = descendants g sym
          cds = S.toList $ S.intersection cs ds
      in map (\cd -> M.findWithDefault (LBool True) cd m) cds

    ind :: Set Symbol -> Symbol -> StateT (Map Symbol Bool) IO Bool
    ind seen sym = do
      memo <- get
      case M.lookup sym memo of
        Just b -> return b
        Nothing ->
          let f = M.findWithDefault (LBool False) sym m
              ps = predecessors g sym
              seen' = S.insert sym seen
          in or <$> sequence
              [ pure $ f == LBool True
              , manyAnd (descs sym) `Z3.entails` f
              , (&&) (null (S.intersection ps seen)) <$> (and <$> mapM (ind seen') (S.toList ps))
              ]
