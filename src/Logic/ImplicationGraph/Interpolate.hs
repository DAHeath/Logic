{-# LANGUAGE TemplateHaskell #-}
module Logic.ImplicationGraph.Interpolate where

import           Control.Lens hiding (Context)
import           Control.Monad.State

import           Data.Data (Data)
import           Data.Graph.Inductive.Graph hiding ((&))
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (fromJust, maybeToList)
import           Data.List (intercalate)
import           Data.List.Split (splitOn)
import           Data.Monoid (Last(Last))

import           Logic.Type as T
import           Logic.Var
import           Logic.Formula
import           Logic.Solver.Z3 (solveChc)
import           Logic.Chc
import           Logic.Model
import           Logic.ImplicationGraph.Type

-- | In order to annotate a implication DAG with invariants, we construct
-- interpolants. In practice, we use Z3's Duality algorithm to solve a system
-- of Constrained Horn Clauses to perform this interpolation.

data EntryRhs
  = RhsInstance Instance
  | RhsQuery Form
  deriving (Show, Read, Eq, Ord, Data)

data LinClause = LinClause Instance ImplGrEdge EntryRhs
  deriving (Show, Read, Eq, Ord, Data)

data ChcState = ChcState
  { _linearClauses :: [LinClause]
  , _andClauses :: Map Node ([Instance], Last (ImplGrEdge, EntryRhs))
  , _orInputs :: Map Node (Last Instance, [Node])
  , _orOutputs :: Map Node [(ImplGrEdge, EntryRhs)]
  } deriving (Show, Read, Eq, Ord, Data)

emptyState :: ChcState
emptyState = ChcState [] M.empty M.empty M.empty

makeLenses ''ChcState

-- | Apply constrained Horn Clause Solving to relabel the nodes with fresh
-- invariants.
interpolate :: ImplGr -> IO (Either Model ImplGr)
interpolate g = solveChc (entailmentChc g) >>= \case
  Left m -> return (Left m)
  Right m -> return (Right $ applyModel m g)

applyModel :: Model -> ImplGr -> ImplGr
applyModel m = nmap node
  where
    node :: ImplGrNode -> ImplGrNode
    node = \case
      InstanceNode i ->
        let fact = M.findWithDefault (LBool True) (i ^. identity, i ^. instanceId) m'
        in InstanceNode (i & formula .~ fact)
      n -> n

    m' :: Map ([Lbl], InstanceId) Form
    m' = M.mapKeys (interpretName . varName) (getModel m)
      where
        interpretName :: Name -> ([Lbl], InstanceId)
        interpretName ('r':rest) =
          let ls = map read (splitOn "_" rest)
          in (init ls, last ls)
        interpretName _ = ([], -1)

-- | Convert an entailment graph into a constrained Horn Clause system.
entailmentChc :: ImplGr -> [Chc]
entailmentChc g =
  let ctxs = ufold (:) [] g                      -- collect the graph contexts
      st = execState (mapM_ ctx ctxs) emptyState -- update the state for each context
  in chcFromState st                             -- convert the state to a chc
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
    (_              , FoldedNode _ ) -> return ()
    (InstanceNode i1, AndNode      ) -> update andClauses n2 ([i1], Last Nothing)
    (InstanceNode i1, OrInputNode  ) -> update orInputs   n2 (Last (Just i1), [])
    (OrInputNode    , OrOutputNode ) -> update orInputs   n1 (Last Nothing, [n2])
    (OrOutputNode   , rhs          ) -> update orOutputs  n1 [(e, rhsNode rhs)]
    (AndNode        , rhs          ) -> update andClauses n1 ([], Last (Just (e, rhsNode rhs)))
    (InstanceNode i1, rhs          ) -> linearClauses %= (:) (LinClause i1 e (rhsNode rhs))
    (_ , _) -> error ("found invalid connection " ++ show l1 ++ " -> " ++ show l2)
  where
    update :: Monoid a => Lens' ChcState (Map Node a) -> Node -> a -> State ChcState ()
    update len n v = len %= M.insertWith mappend n v

    rhsNode :: ImplGrNode -> EntryRhs
    rhsNode = \case
      InstanceNode i -> RhsInstance i
      QueryNode q    -> RhsQuery q
      n              -> error ("invalid rhs " ++ show n)

chcFromState :: ChcState -> [Chc]
chcFromState st =
  map (\(LinClause i e rhs) -> lin i e rhs) (st ^. linearClauses) ++
  andMapChc (st ^. andClauses) ++
  orMapsChc (st ^. orInputs) (st ^. orOutputs)
  where
    -- | Construct a linear Horn Clause.
    lin :: Instance -> ImplGrEdge -> EntryRhs -> Chc
    lin i1 (ImplGrEdge f m) r = case subst m r of
      RhsInstance i2 -> Rule [instanceApp i1] f (instanceApp i2)
      RhsQuery q -> Query [instanceApp i1] f q

    -- | And nodes form non-linear Horn Clauses where all inputs to the node
    -- appear on the LHS of the clause.
    andMapChc :: Map Node ([Instance], Last (ImplGrEdge, EntryRhs)) -> [Chc]
    andMapChc m = do
      (is, Last (Just (ImplGrEdge f m', r))) <- M.elems m
      return $ case subst m' r of
        RhsInstance i' -> Rule (map instanceApp is) f (instanceApp i')
        RhsQuery q -> Query (map instanceApp is) f q

    -- | To construct Horn Clauses from an or relationship, we have to find all
    -- the inputs and outputs to the or node and connect them.
    orMapsChc :: Map Node (Last Instance, [Node]) -> Map Node [(ImplGrEdge, EntryRhs)] -> [Chc]
    orMapsChc inps outs = do
      (Last (Just i), ns) <- M.elems inps
      map (uncurry (lin i)) =<< (maybeToList . (`M.lookup` outs)) =<< ns

    -- | Convert an instance into an applied function.
    instanceApp :: Instance -> App
    instanceApp i =
      let vs = i ^. variables
          name = "r" ++ intercalate "_" (map show (i ^. identity ++ [i ^. instanceId]))
          t = curryType (map typeOf vs) T.Bool
      in App (Free name t) vs
