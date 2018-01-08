module Language.Unstructured.Grammar where

import Control.Lens
import Control.Monad.State
import           Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.List (nub)

import           Logic.Formula hiding (Rule)
import           Language.Unstructured.Unstructured
import           Grammar.Grammar

mkGrammar :: MonadVocab m => Program -> m (Symbol, Grammar)
mkGrammar p = do
  gs <- evalStateT (mapM (procGrammar procMap) procs) (M.empty, length procs)
  pure (controlSymbol $ view _3 $ procMap M.! (p ^. entryPoint), concat gs)
  where
    procs = M.toList $ p ^. procedures
    procMap = M.fromList (zipWith
      (\(pn, (inputs, outputs, _)) loc ->
        (pn, (inputs, outputs, ControlLocation loc loc (inputs ++ outputs)))) procs [0..])

procGrammar :: MonadVocab m
     => Map ProcName ([Var], [Var], ControlLocation)
     -> (ProcName, ([Var], [Var], Imp))
     -> StateT (Map (ProcName, Int) ControlLocation, Symbol) m Grammar
procGrammar procMap (pn, (inps, _, insts)) = do
  -- create a control location for each instruction
  mapM_ controlLocation (zip [0..] insts)
  -- create rules for each instruction
  original <- concat <$> mapM inst (zip [0..] insts)
  -- remove rules with false constraint
  let noFalse = filter (\r -> rhsConstraint (ruleRHS r) /= LBool False) original
  -- attach a rule which enters the procedure unconditionally
  (m, _) <- get
  pure (Rule (m M.! (pn, 0)) (RHS (LBool True) []) : noFalse)

    where
      controlLocation (loc, (_, live)) = do
        (m, i) <- get
        let m' = M.insert (pn, loc) (ControlLocation i i (nub $ inps ++ live)) m
        put (m', i+1)

      inst (loc, (instruction, _)) = case instruction of
        v := f -> do
          (start, t1, f') <- freshenInto loc f
          (end, t2, v') <- freshenInto (loc+1) v

          let car = carry start end t1 t2 (S.singleton v)
          pure [ Rule end (RHS (mkAnd (mkEql (typeOf v') (V v') f') car) [start]) ]

        Call pn' as rs -> do
          let (inputs, outputs, pLoc) = procMap M.! pn'
          (start, t1, ()) <- freshenInto loc ()
          (pExit, t2, ()) <- freshenInst pLoc ()
          (end, t3, ()) <- freshenInto (loc+1) ()
          let args = equate (as & vars %~ t1) (map (V . t2) inputs)
          let outs = equate (map (V . t3) rs) (map (V . t2) outputs)
          let car = carry start end t1 t3 (S.fromList rs)
          pure [ Rule end (RHS (manyAnd [args, outs, car]) [start, pExit]) ]

        Cond f dest -> do
          (start, t1, f') <- freshenInto loc f
          (end1, t2, ()) <- freshenInto dest ()
          (end2, t3, ()) <- freshenInto (loc+1) ()

          let car1 = carry start end1 t1 t2 S.empty
          let car2 = carry start end2 t1 t3 S.empty

          pure [ Rule end1 (RHS (mkAnd f' car1) [start])
               , Rule end2 (RHS (mkAnd (mkNot f') car2) [start]) ]

        Done -> do
          (start, t1, ()) <- freshenInto loc ()
          (end, t2, ()) <- freshenInst (view _3 (procMap M.! pn)) ()
          let car = carry start end t1 t2 S.empty
          pure [ Rule end (RHS car [start]) ]

      freshenInto loc x = do
        (m, _) <- get
        freshenInst (m M.! (pn, loc)) x

      freshenInst i x = do
        point <- freshen M.empty i
        t <- table
        pure (point, t, x & vars %~ t)

      carry start end t1 t2 preserve =
        let svs = S.map unaliasedVar (varSet start)
            evs = S.map unaliasedVar (varSet end)
            pvs = S.map unaliasedVar preserve
            vs = S.toList $ S.difference (svs `S.intersection` evs) pvs
        in equate (map (V . t1) vs) (map (V . t2) vs)

      equate es1 es2 = manyAnd (zipWith (\e1 e2 -> mkEql (typeOf e1) e1 e2) es1 es2)
