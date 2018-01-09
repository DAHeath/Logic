{-# LANGUAGE ScopedTypeVariables #-}
module Grammar.Solve where

import           Control.Lens
import           Control.Monad.Extra (ifM, allM, anyM)
import           Control.Monad.State
import           Control.Monad.Except

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Maybe (fromMaybe)

import           Logic.Formula hiding (Rule)
import qualified Logic.Formula as F
import qualified Logic.Solver.Z3 as Z3

import           Grammar.Grammar
import           Grammar.Unwind

solve :: Grammar -> Form -> IO (Either Model (Map Symbol Form))
solve g f = loop ([], g)
  where
    loop (clones, g) =
      interpolate g f >>= \case
        Left e -> pure (Left e)
        Right m -> ifM (isInductive clones g m)
          (pure (Right m))
          (loop $ unwind (clones, g))

interpolate :: Grammar -> Form -> IO (Either Model (Map Symbol Form))
interpolate g' q =
  let chc = F.Query [app terminal] (LBool True) q : map clause (g ^. grammarRules) in
  runExceptT (interpretModel <$> Z3.solveChc chc)
  where
    g = nonrecursive g'
    terminal = view ruleLHS (head $ rulesFor (g ^. grammarStart)
                                             (g ^. grammarRules)) & vars %~ unaliasedVar
    clause (Rule _ lhs f rhs) = F.Rule (map app rhs) f (app lhs)
    app (Production sym vs) = mkApp ("R" ++ show sym) vs
    interpretModel (Model m) =
      M.mapKeys (read . tail)
      $ M.filterWithKey (\k _ -> head k == 'R')
      $ M.mapKeys _varName m

isInductive :: Clones -> Grammar -> Map Symbol Form -> IO Bool
isInductive clones g m = evalStateT (ind S.empty (g ^. grammarStart)) M.empty
  where
    descs sym =
      let cs = fromMaybe S.empty (cloneFor sym clones)
          ds = descendants (nonrecursive g) sym
          cds = S.toList $ S.intersection cs ds
      in map (\cd -> M.findWithDefault (LBool True) cd m) cds

    ind :: Set Symbol -> Symbol -> StateT (Map Symbol Bool) IO Bool
    ind seen sym = do
      memo <- get
      case M.lookup sym memo of
        Just b -> pure b
        Nothing ->
          let f = M.findWithDefault (LBool False) sym m
              seen' = S.insert sym seen
          in or <$> sequence
              [ pure $ f == LBool True
              , manyAnd (descs sym) `Z3.entails` f
              , indByPred sym seen'
              ]

    indByPred sym seen =
      let ps = predecessors (g ^. grammarRules) sym in
      if | null ps -> pure True
         | null (S.intersection ps seen) ->
           let cats = M.elems (categorize (g ^. grammarRules))
               cps = map (`predecessors` sym) cats :: [Set Symbol]
           in anyM (\(ps' :: Set Symbol) -> allM (ind seen) (S.toList ps')) cps
         | otherwise -> pure False
