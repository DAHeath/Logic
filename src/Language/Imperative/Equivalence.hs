{-# LANGUAGE LambdaCase, FlexibleContexts, QuasiQuotes, TemplateHaskell #-}
module Language.Imperative.Concurrent where

import           Language.Imperative
import           Logic.Type as T
import           Logic.Formula
import           Logic.Model
import           Logic.Formula.Parser
import           Logic.Chc
import           Logic.Solver.Z3

import           Control.Monad
import           Control.Monad.Extra
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Lens

import           Data.Graph.Inductive.Basic
import           Data.Graph.Inductive.Graph
import           Data.Graph.Inductive.PatriciaTree
import           Data.Graph.Inductive.Extras
import qualified Data.Map as M
import           Data.Map (Map)
import qualified Data.Set as S
import           Data.Set (Set)

import           Extra (splitOn)

import           Text.Read (readMaybe)
import           Text.PrettyPrint.HughesPJClass (prettyShow)

import Debug.Trace

-- TODO there is a simplification in the current implementation which says that
-- the initial node of the graph stays the same regardless of unfoldings. This
-- is not in general true, since it is possible (though it would be somewhat odd)
-- for the initial node to be included in an unfolding.

data DagState = DagState
  { firstLbl :: Map Node Lbl
  , lastLbl :: Map Node Lbl
  , currentLbl :: Lbl
  } deriving (Show, Eq, Ord)

mkLbl :: State DagState Lbl
mkLbl = do
  l <- currentLbl <$> get
  modify (\s -> s { currentLbl = l + 1 })
  return (l + 1)

newDagState :: DagState
newDagState = DagState M.empty M.empty (-1)

-- dagTransitions :: Gr (Set Var) SemAct -> ([(Lbl, Lbl, SemAct)], Lbl)
-- dagTransitions g = evalState (do
--   ns <- traverse nodeTransitions (labNodes g)
--   es <- traverse edgeTransitions (labEdges g)
--   final <- currentLbl <$> get
--   return (es ++ concat ns, final)) newDagState
--   where
--     nodeTransitions (n, bb) = do
--       f <- mkLbl
--       modify (\s -> s { firstLbl = M.insert n f (firstLbl s) })
--       ts <- traverse assign bb
--       l <- currentLbl <$> get
--       modify (\s -> s { lastLbl = M.insert n l (lastLbl s) })
--       return ts

--     edgeTransitions (l1, l2, e) = do
--       start <- M.findWithDefault undefined l1 <$> (lastLbl <$> get)
--       end <- M.findWithDefault undefined l2 <$> (firstLbl <$> get)
--       return (start, end, e)

--     assign (v, rhs) = do
--       start <- currentLbl <$> get
--       end <- mkLbl
--       return (start, end, Assign v rhs)

data Which = L | R
  deriving (Show, Eq, Ord)


equivalentGraphsChc :: Gr (Set Var) SemAct
                    -> Gr (Set Var) SemAct
                    -> [Chc]
equivalentGraphsChc = undefined

-- | Given a pair of imperative DAGs, construct a CHC system which encodes
-- the conccurrent execution of the two.
-- concurrentGraphsChc :: (Set Var, Gr BasicBlock Body) -> (Set Var, Gr BasicBlock Body) -> [Chc]
-- concurrentGraphsChc (vs1, g1) (vs2, g2) =
--   let (ts1, ls1) = dagTransitions g1
--       (ts2, ls2) = dagTransitions g2 in
--   (do (l1, l2, b) <- ts1
--       fixed <- [0..ls2]
--       return $ rule L vs1 vs2 l1 l2 fixed b) ++
--   (do (l1, l2, b) <- ts2
--       fixed <- [0..ls1]
--       return $ rule R vs1 vs2 l1 l2 fixed b)

rule :: Which -> Set Var -> Set Var -> Lbl -> Lbl -> Lbl -> SemAct -> Chc
rule w vs1 vs2 l1 l2 fixed = \case
  Cond f ->
    Rule [a1 vars] f (a2 vars)
  Assign v rhs ->
    let v' = v { varName = '$' : varName v }
        hd = a2 (map (\v'' -> if v == v'' then v' else v'') vars)
        body = case rhs of
          Expr f -> app2 (Eql (typeOf v)) (V v') f
          Arbitrary _ -> LBool True
    in Rule [a1 vars] body hd
  where
    vars = S.toList $ S.union vs1 vs2
    a1 vs = case w of
      L -> mkApp vs l1 fixed
      R -> mkApp vs fixed l1
    a2 vs = case w of
      L -> mkApp vs l2 fixed
      R -> mkApp vs fixed l2

mkApp :: [Var] -> Lbl -> Lbl -> App
mkApp vs l1 l2 =
  let n = "r" ++ show l1 ++ "_" ++ show l2
  in App (Var (curryType (map typeOf vs) T.Bool) n) vs

-- fullChc =
--   let g1 = graph proc1
--       g2 = graph proc2
--       x = Var T.Int "x"
--       s = Var T.Int "s"
--       n = Var T.Int "n"
--       vs1 = S.fromList [x, n, s]
--       vs2 = S.fromList [s]
--   in
--   concurrentGraphsChc (vs1, getFlowGraph g1) (vs2, getFlowGraph g2)

testChc =
  let FlowGraph g1 i1 t1 = graph proc1
      FlowGraph g2 i2 t2 = graph proc2
      bs = backEdges g1
      (g', dup) = runState (
        do h <- unfold (head $ backEdges g1) g1
           unfold (head $ backEdges g1) h)
           mempty
      g1' = efilter (`notElem` bs) g'
      g1'' = reverseReached t1 g1'
      g2' = reverseReached t2 g2
      x = Var T.Int "x"
      s = Var T.Int "s"
      n = Var T.Int "n"
      vs1 = S.fromList [x, n, s]
      vs2 = S.fromList [s]
      vars = S.toList $ S.union vs1 vs2

      start = Var (T.Int :=> T.Int :=> T.Int :=> T.Bool) "r0_0"
      end = Var (T.Int :=> T.Int :=> T.Int :=> T.Bool) "r7_1"
  in
  Rule [] [form|s:Int = 0 && n:Int = 2|] (App start vars) :
  concurrentGraphsChc (vs1, g1'') (vs2, g2')
  ++ [Query [App end vars] (LBool True) [form| s:Int = (2* n:Int) + 1 |]]

type InvariantMap = Map (Lbl, Lbl) Form

data PairState = PairState
  { _currentG1 :: Gr BasicBlock Body
  , _currentG2 :: Gr BasicBlock Body
  , _duplicates1 :: DuplicationMap
  , _duplicates2 :: DuplicationMap
  , _invariants :: InvariantMap
  } deriving (Show, Eq)

makeLenses ''ConcurrencyState

-- toDag :: Node -> [LEdge Body] -> Gr BasicBlock Body -> Gr BasicBlock Body
-- toDag t bs g = reverseReached t $ efilter (`notElem` bs) g

-- relNameToPair :: String -> Maybe (Lbl, Lbl)
-- relNameToPair n =
--   undefined


-- modelToInvMap :: Model -> InvariantMap
-- modelToInvMap (Model m) = undefined

-- concurrent :: MonadIO m => Set Var -> Form -> Form -> Proc -> Proc -> m (Either Model InvariantMap)
-- concurrent vs initCond phi p1 p2 =
--     evalStateT (runExceptT concurrent')
--                (ConcurrencyState (getFlowGraph g1) (getFlowGraph g2) M.empty M.empty M.empty)

--   where
--     g1 = graph p1
--     g2 = graph p2
--     bs1 = backEdges (getFlowGraph g1)
--     bs2 = backEdges (getFlowGraph g2)

--     intro = Rule [] initCond (mkApp (S.toList vs) (initial g1) (initial g2))
--     query = Query [mkApp (S.toList vs) (terminal g1) (terminal g2)] (LBool True) phi
--     ctx = [intro, query]
--     fullChc = ctx ++ concurrentGraphsChc (vs, getFlowGraph g1) (vs, getFlowGraph g2)

--     concurrent' :: (MonadIO m, MonadError Model m, MonadState ConcurrencyState m) => m InvariantMap
--     concurrent' = do
--       g1' <- toDag (terminal g1) bs1 <$> use currentG1
--       g2' <- toDag (terminal g2) bs2 <$> use currentG2
--       let chc = ctx ++ concurrentGraphsChc (vs, g1') (vs, g2')
--       m <- solveChc chc
--       m' <- either throwError return m
--       liftIO $ print m'
--       let m'' = modelToInvMap m'
--       liftIO $ print m''
--       mergeInvariants m''
--       ifM (coverCheck fullChc)
--         (use invariants) $ do
--           mapM_ unfoldG1 bs1
--           mapM_ unfoldG2 bs2
--           concurrent'

-- coverCheck :: (MonadIO m, MonadState ConcurrencyState m) => [Chc] -> m Bool
-- coverCheck = undefined

-- unfoldG1, unfoldG2 :: MonadState ConcurrencyState m => LEdge Body -> m ()
-- unfoldG1 e = do
--   g <- use currentG1
--   d <- use duplicates1
--   let (g', d') = runState (unfold e g) d
--   currentG1 .= g'
--   duplicates1 .= d'
-- unfoldG2 e = do
--   g <- use currentG2
--   d <- use duplicates2
--   let (g', d') = runState (unfold e g) d
--   currentG2 .= g'
--   duplicates2 .= d'


-- mergeInvariants :: MonadState ConcurrencyState m => InvariantMap -> m ()
-- mergeInvariants newIs = do
--   dups1 <- use duplicates1
--   dups2 <- use duplicates2
--   invs <- use invariants
--   let resolve (loc1, loc2) = (dupLookup dups1 loc1, dupLookup dups2 loc2)
--   let folded = M.foldWithKey (\k v m -> M.insertWith (app2 Or) (resolve k) v m) newIs M.empty
--   let invs' = M.unionWith (app2 Or) folded invs
--   invariants .= invs'

-- disp sys = mapM_ (print . prettyShow) sys

-- fullTest = putStrLn . prettyShow =<< solveChc testChc

-- procTest :: IO (Either Model InvariantMap)
-- procTest =
--   let vs = S.fromList [x, n, s]
--       x = Var T.Int "x"
--       s = Var T.Int "s"
--       n = Var T.Int "n"
--       initCond = [form|s:Int = 0 && n:Int = 2|]
--       query = [form| s:Int = (2* n:Int) + 1 |]
--   in concurrent vs initCond query proc1 proc2
