module Grammar.Solve where

import           Control.Lens
import           Control.Monad.Extra (ifM)
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



import           Data.Text.Prettyprint.Doc

solve :: Grammar -> Form -> IO (Either Model (Map Symbol Form))
solve g f = loop ([], g)
  where
    loop (clones, g) = do
      print (pretty g)
      res <- interpolate g f
      case res of
        Left e -> return (Left e)
        Right m -> ifM (isInductive clones g m)
          (return (Right m))
          (loop $ unwind (clones, g))

interpolate :: Grammar -> Form -> IO (Either Model (Map Symbol Form))
interpolate g' q =
  let chc = F.Query [app term] (LBool True) q : map clause (g ^. grammarRules) in
  runExceptT (interpretModel <$> Z3.solveChc chc)
  where
    term = view ruleLHS (head $ rulesFor (g ^. grammarStart)
                                         (g ^. grammarRules)) & vars %~ unaliasedVar
    g = nonrecursive g'
    clause (Rule lhs f rhs) = F.Rule (map app rhs) f (app lhs)
    app (Production sym vs) = mkApp ("R" ++ show sym) vs
    interpretModel (Model m) =
      M.mapKeys (read . tail)
      $ M.filterWithKey (\k _ -> head k == 'R')
      $ M.mapKeys _varName m

isInductive :: Clones -> Grammar -> Map Symbol Form -> IO Bool
isInductive clones g m = do
  print (pretty (M.toList m))
  evalStateT (ind S.empty (g ^. grammarStart)) M.empty
  where
    descs sym =
      let cs = fromMaybe S.empty (cloneFor sym clones)
          ds = S.filter (/= sym) (descendants g sym)
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
          in do
          liftIO $ print (pretty (descs sym))
          or <$> sequence
              [ pure $ f == LBool True
              , manyAnd (descs sym) `Z3.entails` f
              , indByPred ps seen'
              ]

    indByPred ps seen =
      if null (S.intersection ps seen)
      then and <$> mapM (ind seen) (S.toList ps)
      else pure False
