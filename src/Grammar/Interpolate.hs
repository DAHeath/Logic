module Grammar.Interpolate where

import           Control.Lens
import           Control.Monad.Except

import           Data.Map (Map)
import qualified Data.Map as M

import           Logic.Formula hiding (Rule)
import qualified Logic.Formula as F
import qualified Logic.Solver.Z3 as Z3
import           Grammar.Grammar
import           Grammar.Unwind

interpolate :: Grammar -> Form -> IO (Either Model (Map Symbol Form))
interpolate g' q =
  runExceptT (interpretModel <$>
    Z3.solveChc (F.Query [app term] (LBool True) q : map clause (g ^. grammarRules)))
  where
    term = view ruleLHS $ head $ rulesFor (g ^. grammarStart)
                                          (g ^. grammarRules) & vars %~ unaliasedVar
    g = nonrecursive g'
    clause (Rule lhs f rhs) = F.Rule (map app rhs) f (app lhs)
    app (Production sym vs) = mkApp ("R" ++ show sym) vs
    interpretModel (Model m) =
      M.mapKeys (read . tail)
      $ M.filterWithKey (\k _ -> head k == 'R')
      $ M.mapKeys _varName m
