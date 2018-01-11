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

import           Formula hiding (Rule)
import qualified Formula as F
import qualified Formula.Z3 as Z3

import           Grammar.Grammar
import           Grammar.Unwind
import           Grammar.Plot

solve :: Grammar -> Expr -> IO (Either Model (Map Symbol Expr))
solve g f = loop ([], g)
  where
    loop (clones, g') = interpolate g' f >>= \case
      Left e -> pure (Left e)
      Right m -> ifM (isInductive clones g' m)
        (pure (Right m))
        (loop $ unwind (clones, g'))

interpolate :: Grammar -> Expr -> IO (Either Model (Map Symbol Expr))
interpolate g' q =
  let clauses = F.Query [app terminal] (LBool True) q : map clause (g ^. grammarRules) in
  runExceptT (interpretModel <$> Z3.solveChc clauses)
  where
    g = nonrecursive g'
    terminal = view ruleLHS (head $ rulesFor (g ^. grammarStart)
                                             (g ^. grammarRules)) & vars %~ unaliasedVar
    clause (Rule _ lhs f rhs) = F.Rule (map app rhs) f (app lhs)
    app (Production sym vs) = mkApp ("R" ++ show sym) vs
    interpretModel m =
      M.mapKeys (read . tail)
      $ M.filterWithKey (\k _ -> head k == 'R')
      $ M.mapKeys _varName m

isInductive :: Clones -> Grammar -> Map Symbol Expr -> IO Bool
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
          (at sym <?=) =<<
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
               cps = map (`predecessors` sym) cats
           in anyM (allM (ind seen) . S.toList) cps
         | otherwise -> pure False
