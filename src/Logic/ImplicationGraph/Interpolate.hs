{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}
module Logic.ImplicationGraph.Interpolate where

import           Control.Lens hiding (Context)
import           Control.Monad.State

import           Data.Data (Data)
import           Data.Graph.Inductive.Graph hiding ((&))
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (fromJust)
import           Data.List (intercalate)
import           Data.List.Split (splitOn)

import           Logic.Type as T
import           Logic.Var
import           Logic.Formula
import           Logic.Solver.Z3
import           Logic.Chc
import           Logic.Model
import           Logic.ImplicationGraph.Type

data EntryRhs
  = RhsInstance Instance
  | RhsQuery Form
  deriving (Show, Read, Eq, Ord, Data)

data LinClause = LinClause Instance ImplGrEdge EntryRhs
  deriving (Show, Read, Eq, Ord, Data)

data ChcState = ChcState
  { _linearClauses :: [LinClause]
  , _andClauses :: Map Node ([Instance], Maybe (ImplGrEdge, EntryRhs))
  , _orInputs :: Map Node (Maybe Instance, [Node])
  , _orOutputs :: Map Node [(ImplGrEdge, EntryRhs)]
  } deriving (Show, Read, Eq, Ord, Data)

emptyState :: ChcState
emptyState = ChcState [] M.empty M.empty M.empty

makeLenses ''ChcState

-- | Apply constrained Horn Clause Solving to relabel the nodes with fresh
-- invariants.
interpolate :: ImplGr -> IO (Either Model ImplGr)
interpolate g = do
  let sys = entailmentChc g
  sol <- solveChc sys
  case sol of
    Left m -> return (Left m)
    Right m -> return (Right $ applyModel m g)

applyModel :: Model -> ImplGr -> ImplGr
applyModel m = nmap node
  where
    node = \case
      InstanceNode i ->
        let fact = M.findWithDefault (LBool True) (i ^. identity, i ^. instanceId) m'
        in InstanceNode (i & formula .~ fact)
      n -> n
    m' = interpretModel m

interpretModel :: Model -> Map ([Lbl], InstanceId) Form
interpretModel (Model m) = M.mapKeys (interpretName . varName) m
  where
    interpretName :: Name -> ([Lbl], InstanceId)
    interpretName ('r':rest) =
      let ls = map read (splitOn "_" rest)
      in (init ls, last ls)
    interpretName _ = ([], -1)

-- | Convert an entailment graph into a constrained Horn Clause system.
entailmentChc :: ImplGr -> [Chc]
entailmentChc g =
  let ctxs = ufold (:) [] g
      st = execState (mapM_ ctx ctxs) emptyState
  in chcFromState st
  where
    -- | Given the context for some node, update the state.
    ctx :: Context ImplGrNode ImplGrEdge -> State ChcState ()
    ctx (bef, n, here, aft) = do
      mapM_ connect (zip3 (map (node . snd) bef) (map fst bef) (repeat (n, here)))
      mapM_ connect (zip3 (repeat (n, here)) (map fst aft) (map (node . snd) aft))

    node :: Node -> (Node, ImplGrNode)
    node n = (n, fromJust $ lab g n)

    -- | Each edge in the entailment represents either a linear Horn Clause
    -- (between instance and instance nodes or instance and query nodes) or a
    -- portion of some complex relationship.
    connect :: ((Node, ImplGrNode), ImplGrEdge, (Node, ImplGrNode)) -> State ChcState ()
    connect ((n1, l1), e, (n2, l2)) =
      case (l1, l2) of
        (InstanceNode i1, InstanceNode i2) -> linearClauses %= (:) (LinClause i1 e (RhsInstance i2))
        (InstanceNode i1, QueryNode q2) -> linearClauses %= (:) (LinClause i1 e (RhsQuery q2))
        (AndNode _, InstanceNode i2) -> updateAndRhs n1 e (RhsInstance i2)
        (AndNode _, QueryNode q2) -> updateAndRhs n1 e (RhsQuery q2)
        (InstanceNode i1, AndNode _) -> do
          m <- use andClauses
          andClauses %= case M.lookup n2 m of
            Nothing -> M.insert n2 ([i1], Nothing)
            Just (lhs, rhs) -> M.insert n2 (i1 : lhs, rhs)
        (InstanceNode i1, OrInputNode _) -> do
          m <- use orInputs
          orInputs %= case M.lookup n2 m of
            Nothing -> M.insert n2 (Just i1, [])
            Just (_, rhs) -> M.insert n2 (Just i1, rhs)
        (OrInputNode _, OrOutputNode _) -> do
          m <- use orInputs
          orInputs %= case M.lookup n1 m of
            Nothing -> M.insert n1 (Nothing, [n2])
            Just (lhs, rhs) -> M.insert n1 (lhs, n2 : rhs)
        (OrOutputNode _, InstanceNode i2) -> updateOrOutput n1 e (RhsInstance i2)
        (OrOutputNode _, QueryNode q2) -> updateOrOutput n1 e (RhsQuery q2)
        (_, FoldedNode _) -> return ()
        (_, _) -> error ("found invalid connection " ++ show g)

    -- | Update (or create) the entry for the `and` node by setting the RHS.
    updateAndRhs n e r = do
      m <- use andClauses
      andClauses %= case M.lookup n m of
        Nothing -> M.insert n ([], (Just (e, r)))
        Just (lhs, _) -> M.insert n (lhs, (Just (e, r)))

    -- | Update (or create) the entry for an `or` output node by augmenting the RHS.
    updateOrOutput n e r = do
      m <- use orOutputs
      orOutputs %= case M.lookup n m of
        Nothing -> M.insert n [(e, r)]
        Just l -> M.insert n ((e, r):l)

    chcFromState :: ChcState -> [Chc]
    chcFromState st =
      map (\(LinClause i e rhs) -> lin i e rhs) (st ^. linearClauses) ++
      andMapChc (st ^. andClauses) ++
      orMapsChc (st ^. orInputs) (st ^. orOutputs)

    -- | Construct a linear Horn Clause.
    lin :: Instance -> ImplGrEdge -> EntryRhs -> Chc
    lin i1 (ImplGrEdge f m) r =
      let r' = subst m r
      in case r' of
        RhsInstance i2 -> Rule [instanceApp i1] f (instanceApp i2)
        RhsQuery q -> Query [instanceApp i1] f q

    andMapChc :: Map Node ([Instance], Maybe (ImplGrEdge, EntryRhs)) -> [Chc]
    andMapChc m = concatMap andChc (M.elems m)

    andChc :: ([Instance], Maybe (ImplGrEdge, EntryRhs)) -> [Chc]
    andChc (is, Just (ImplGrEdge f m, r)) =
      let r' = subst m r
      in case r' of
        RhsInstance i' -> [Rule (map instanceApp is) f (instanceApp i')]
        RhsQuery q -> [Query (map instanceApp is) f q]
    andChc _ = error "incomplete and clause"

    orMapsChc :: Map Node (Maybe Instance, [Node])
              -> Map Node [(ImplGrEdge, EntryRhs)]
              -> [Chc]
    orMapsChc inps outs = concatMap (orChc outs) (M.elems inps)

    orChc :: Map Node [(ImplGrEdge, EntryRhs)]
          -> (Maybe Instance, [Node])
          -> [Chc]
    orChc outs (Just i, ns) = concatMap (orClause outs i) ns
    orChc _ _ = error "incomplete or clause"

    orClause :: Map Node [(ImplGrEdge, EntryRhs)] -> Instance -> Node -> [Chc]
    orClause m i n = case M.lookup n m of
      Just rhs -> map (uncurry (lin i)) rhs
      Nothing -> error "incomplete or clause"

    -- | Convert an instance into an applied function.
    instanceApp :: Instance -> App
    instanceApp i =
      let vs = i ^. variables
          name = "r" ++ intercalate "_" (map show (i ^. identity ++ [i ^. instanceId]))
          t = curryType (map typeOf vs) T.Bool
      in App (Free name t) vs

