{-# LANGUAGE TemplateHaskell #-}
module Logic.ImplicationGraph.Interpolate where

import           Control.Lens hiding (Context)
import           Control.Monad.State

import           Data.Data (Data)
import qualified Data.Ord.Graph as G
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

import           Text.PrettyPrint.HughesPJClass (prettyShow)

-- | In order to annotate a implication DAG with invariants, we construct
-- interpolants. In practice, we use Z3's Duality algorithm to solve a system
-- of Constrained Horn Clauses to perform this interpolation.

data EntryRhs
  = RhsInstance (Node, Instance)
  | RhsQuery Form
  deriving (Show, Read, Eq, Ord, Data)

data LinClause = LinClause Node Instance ImplGrEdge EntryRhs
  deriving (Show, Read, Eq, Ord, Data)

data ChcState = ChcState
  { _linearClauses :: [LinClause]
  , _andClauses :: Map Node ([(Node, Instance)], Last (ImplGrEdge, EntryRhs))
  , _orInputs :: Map Node (Last Instance, [Node])
  , _orOutputs :: Map Node [(ImplGrEdge, EntryRhs)]
  } deriving (Show, Read, Eq, Ord, Data)

emptyState :: ChcState
emptyState = ChcState [] M.empty M.empty M.empty

makeLenses ''ChcState

-- | Apply constrained Horn Clause Solving to relabel the nodes with fresh
-- invariants.
interpolate :: ImplGr -> IO (Either Model ImplGr)
interpolate g = do
  let chc = entailmentChc g
  solveChc chc >>= \case
    Left m -> return (Left m)
    Right m -> return (Right $ applyModel m g)

applyModel :: Model -> ImplGr -> ImplGr
applyModel m = G.imapVerts node
  where
    node :: Node -> ImplGrNode -> ImplGrNode
    node i = \case
      InstanceNode (vs, _) ->
        let fact = M.findWithDefault (LBool True) i m'
        in InstanceNode (vs, fact)
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
  chcFromState $ execState (mapM_ connect (G.connections g)) emptyState

-- | Each edge in the entailment represents either a linear Horn Clause
-- (between instance and instance nodes or instance and query nodes) or a
-- portion of some complex relationship.
connect :: ((Node, ImplGrNode), ImplGrEdge, (Node, ImplGrNode)) -> State ChcState ()
connect ((n1, l1), e, (n2, l2)) =
  case (l1, l2) of
    (_              , FoldedNode _ ) -> return ()
    (InstanceNode i1, AndNode      ) -> update andClauses n2 ([(n1, i1)], Last Nothing)
    (InstanceNode i1, OrInputNode  ) -> update orInputs   n2 (Last (Just i1), [])
    (OrInputNode    , OrOutputNode ) -> update orInputs   n1 (Last Nothing, [n2])
    (OrOutputNode   , rhs          ) -> update orOutputs  n1 [(e, rhsNode n2 rhs)]
    (AndNode        , rhs          ) -> update andClauses n1 ([], Last (Just (e, rhsNode n2 rhs)))
    (InstanceNode i1, rhs          ) -> linearClauses %= (:) (LinClause n1 i1 e (rhsNode n2 rhs))
    (_ , _) -> error ("found invalid connection " ++ show l1 ++ " -> " ++ show l2)
  where
    update :: Monoid a => Lens' ChcState (Map Node a) -> Node -> a -> State ChcState ()
    update len n v = len %= M.insertWith mappend n v

    rhsNode :: Node -> ImplGrNode -> EntryRhs
    rhsNode n = \case
      InstanceNode i -> RhsInstance (n, i)
      QueryNode q    -> RhsQuery q
      n              -> error ("invalid rhs " ++ show n)

chcFromState :: ChcState -> [Chc]
chcFromState st =
  map (\(LinClause n1 i e rhs) -> lin n1 i e rhs) (st ^. linearClauses) ++
  andMapChc (st ^. andClauses) ++
  orMapsChc (st ^. orInputs) (st ^. orOutputs)
  where
    -- | Construct a linear Horn Clause.
    lin :: Node -> Instance -> ImplGrEdge -> EntryRhs -> Chc
    lin n1 i1 (ImplGrEdge f m) r = case subst m r of
      RhsInstance (n2, i2) -> Rule [instanceApp n1 i1] f (instanceApp n2 i2)
      RhsQuery q -> Query [instanceApp n1 i1] f q

    -- | And nodes form non-linear Horn Clauses where all inputs to the node
    -- appear on the LHS of the clause.
    andMapChc :: Map Node ([(Node, Instance)], Last (ImplGrEdge, EntryRhs)) -> [Chc]
    andMapChc m = do
      (is, Last (Just (ImplGrEdge f m', r))) <- M.elems m
      return $ case subst m' r of
        RhsInstance (n2, i') -> Rule (map (uncurry instanceApp) is) f (instanceApp n2 i')
        RhsQuery q -> Query (map (uncurry instanceApp) is) f q

    -- | To construct Horn Clauses from an or relationship, we have to find all
    -- the inputs and outputs to the or node and connect them.
    orMapsChc :: Map Node (Last Instance, [Node]) -> Map Node [(ImplGrEdge, EntryRhs)] -> [Chc]
    orMapsChc inps outs = do
      (n1, (Last (Just i), ns)) <- M.toList inps
      map (uncurry (lin n1 i)) =<< (maybeToList . (`M.lookup` outs)) =<< ns

    -- | Convert an instance into an applied function.
    instanceApp :: Node -> Instance -> App
    instanceApp (iden, inst) (vs, _) =
      let name = "r" ++ intercalate "_" (map show (iden ++ [inst]))
          t = curryType (map typeOf (concat vs)) T.Bool
      in App (Free name t) (concat vs)
