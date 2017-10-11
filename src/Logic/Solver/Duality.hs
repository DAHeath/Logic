{-# LANGUAGE TemplateHaskell, TupleSections #-}
module Logic.Solver.Duality where

import           Control.Monad.State
import           Control.Monad.Except
import           Control.Monad.Extra (ifM)
import           Control.Arrow (second)
import           Control.Lens hiding (children, (&))

import           Data.Foldable (traverse_)
import           Data.Graph.Inductive.Graph
import           Data.Graph.Inductive.PatriciaTree
import           Data.Graph.Inductive.Extras
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Tree (Tree)
import qualified Data.Tree as T
import           Data.Tree.Extras
import           Data.Random

import           Logic.Type
import           Logic.Formula
import           Logic.Var
import           Logic.Model
import           Logic.Chc
import qualified Logic.Solver.Z3 as Z3

-- TODO
-- rapid convergence via generalization
-- quickly choosing appropriate children
-- non-random children choice

data Instance = Instance
  { instanceBackground :: Chc
  , instanceDefinition :: Form
  } deriving (Show, Eq, Ord)

type DAG v = Gr v ()

data DualityState = DualityState
  { _instanceGraph :: DAG Instance
  , _predicateInstances :: Map Var [Node]
  , _instances :: Map Chc (Set (Set Node))
  , _preds :: [Var]
  } deriving (Show, Eq)

newDualityState :: [Chc] -> DualityState
newDualityState chc = DualityState empty mempty mempty (concatMap predicates chc)

makeLenses ''DualityState

type HasDualityState a = forall m. MonadState DualityState m => m a
type Duality a = forall m. (MonadError Model m, MonadState DualityState m, MonadIO m) => m a

-- | Solve the Relational Post Fixed-Point Problem. That is, given a system of
-- constrained Horn Clauses, generate a Model. The Model is either:
-- + A valid interpretation of the predicates in the original system such that
--   using the interpretation makes the system hold.
-- + A counterexample derivation with assignments to various instances of the
--   variables in the CHC system.
duality :: MonadIO m => [Chc] -> m (Either Model Model)
duality chc = evalStateT (runExceptT loop) (newDualityState chc)
  where
    loop :: Duality Model
    loop = ifM (and <$> traverse step chc) model loop

step :: Chc -> Duality Bool
step clause = do
  f <- applyChc <$> (applyModelToApp <$> model) <*> pure clause
  ifM (Z3.isValid f) (return True)
                  (action clause >> return False)

-- When a particular rule iinvalid , what is the action that we take?
action :: Chc -> Duality ()
action clause = case clause of
  -- When a rule is invalid, we add a new instance
  r@(Rule _ _ rhs) -> newInstance r (appOperator rhs)
  -- When a query is invalid, we perform tree interpolation on a failure
  -- derivation and update the definitions of the instances.
  q@Query{} -> do
    t <- derivationTree q
    itp <- Z3.interpolate (fmap (\(_, x, _) -> x) t)
    case itp of
      Left m -> throwError m
      Right itp' -> updateGraph (zipTree abstractNode t itp')

-- The instance definitions are meant to be stored in abstract form.
abstractNode :: (Node, Form, [Var]) -> Form -> (Node, Form)
abstractNode (idx, _, vs) f = (idx, abstract vs f)

-- Construct the current model from the instance graph.
model :: HasDualityState Model
model = do
  prs <- use preds
  (Model . M.fromList) <$> traverse
    (\p -> do fs <- map instanceDefinition <$> instancesOf p
              return (p, if null fs then LBool False else manyOr fs)) prs

-- In adding a new instance to the graph, we have to select which children
-- to use. We must take care not to reproduce an instance which already exists.
selectChildren :: Chc -> Duality [Node]
selectChildren clause = do
  let apps = chcLhs clause
  cs <- traverse (pick <=< instanceKeys) (map appOperator apps)
  insts <- M.findWithDefault S.empty clause <$> use instances
  if S.fromList cs `elem` insts
  then selectChildren clause
  else do
    instances %= M.insertWith S.union clause (S.singleton (S.fromList cs))
    return cs

derivationTree :: Chc -> Duality (Tree (Node, Form, [Var]))
derivationTree clause = do
  cs <- selectChildren clause
  g <- use instanceGraph
  let ts = map (`treeFrom` g) cs
  return $ formTree (chcTree ts) []

  where
    chcTree t =
      let t' = T.Node (-1, clause) $ map (fmap (second instanceBackground)) t in
      evalState (traverse (\(i, cla) -> (i,) <$> relabelChc cla) t') 0

    formTree (T.Node (x, chc) cs) vs =
      let chc' = subst (M.fromList $ zip (chcBindings chc) vs) chc
          vs' = chcBindings chc'
          cs' = zipWith (\n app -> formTree n (appOperands app)) cs (chcLhs chc')
      in
      T.Node (x, chcContext chc', vs') cs'

newInstance :: Chc -> Var -> Duality ()
newInstance clause oper = do
  cs <- selectChildren clause
  [n] <- newNodes 1 <$> use instanceGraph
  let ctx = ([], n, Instance clause (LBool True), zip (repeat ()) cs)
  instanceGraph %= (ctx &)
  predicateInstances %= M.insertWith (++) oper [n]

updateGraph :: Tree (Node, Form) -> Duality ()
updateGraph =
  traverse_ (\(i, f) ->
    unless (i < 0) $ updateNode i f)
  where
    updateNode :: Node -> Form -> Duality ()
    updateNode idx f = do
      v <- vertex idx <$> use instanceGraph
      let v' = v { instanceDefinition = mappend f (instanceDefinition v) }
      instanceGraph %= setVertex idx v'

setVertex :: Node -> a -> Gr a b -> Gr a b
setVertex n x = gmap
  (\(bf, n', y, af) -> if n == n' then (bf, n, x, af) else (bf, n', y, af))

relabelChc :: MonadState Int m => Chc -> m Chc
relabelChc q@Query{} = return q
relabelChc r =
  let bound = S.fromList $ chcBindings r
      vs = varSet r
      free = vs S.\\ bound
  in do
    fc <- get
    let (m, fc') = foldr (\v (m', c) ->
          let newV = Free (varName v ++ "__" ++ show c) (typeOf v) in
          (M.insert v newV m', c+1)) (M.empty, fc) free
    put fc'
    return $ subst m r

instanceKeys :: Var -> HasDualityState [Node]
instanceKeys v = M.findWithDefault [] v <$> use predicateInstances

instancesOf :: Var -> HasDualityState [Instance]
instancesOf v = do
  g <- use instanceGraph
  map (`vertex` g) <$> instanceKeys v

pick :: MonadIO m => [a] -> m a
pick xs = liftIO $ runRVar (randomElement xs) StdRandom
