module Logic.ImplicationGraph.Solve where

import           Control.Lens hiding (Context)

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
import           Text.PrettyPrint.HughesPJClass

data EntryRhs
  = RhsInstance Instance
  | RhsQuery Form
  deriving (Show, Read, Eq, Ord, Data)

data ComplexClauseEntry
  = AndClause [Instance] (Maybe (ImplGrEdge, EntryRhs))
  | OrClause (Maybe Instance) [(ImplGrEdge, EntryRhs)]
  deriving (Show, Read, Eq, Ord, Data)

data LinClause = LinClause Instance ImplGrEdge EntryRhs
  deriving (Show, Read, Eq, Ord, Data)

type ChcState = ([LinClause], Map Node ComplexClauseEntry)

-- | Apply constrained Horn Clause Solving to relabel the nodes with fresh
-- invariants.
solve :: ImplGr -> IO (Either Model ImplGr)
solve g = do
  let sys = entailmentChc g
  putStrLn (prettyShow sys)
  sol <- solveChc sys
  case sol of
    Left m -> return (Left m)
    Right m -> do
      putStrLn (prettyShow m)
      return (Right $ applyModel m g)

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
entailmentChc g = chcFromState $ ufold ctx ([], M.empty) g
  where
    -- | Given the context for some node, update the state by augmenting new
    -- linear Horn Clauses and adding new or modifiying existing complex clauses.
    ctx (bef, n, here, aft) st1 =
      let st2 = foldr connect st1 (zip3 (map (node . snd) bef) (map fst bef) (repeat (n, here)))
          st3 = foldr connect st2 (zip3 (repeat (n, here)) (map fst aft) (map (node . snd) aft))
      in st3

    node :: Node -> (Node, ImplGrNode)
    node n = (n, fromJust $ lab g n)

    -- | Each edge in the entailment represents either a linear Horn Clause
    -- (between instance and instance nodes or instance and query nodes) or a
    -- portion of some complex relationship.
    connect :: ((Node, ImplGrNode), ImplGrEdge, (Node, ImplGrNode))
            -> ChcState -> ChcState
    connect ((n1, l1), e, (n2, l2)) (cs, m) =
      case (l1, l2) of
        (InstanceNode i1, InstanceNode i2) -> (LinClause i1 e (RhsInstance i2) : cs, m)
        (InstanceNode i1, QueryNode q2) -> (LinClause i1 e (RhsQuery q2) : cs, m)
        (AndNode _, InstanceNode i2) -> (cs, updateAndRhs m n1 e (RhsInstance i2))
        (AndNode _, QueryNode q2) -> (cs, updateAndRhs m n1 e (RhsQuery q2))
        (InstanceNode i1, AndNode _) ->
          case M.lookup n2 m of
            Nothing -> (cs, M.insert n2 (AndClause [i1] Nothing) m)
            Just (AndClause lhs rhs) -> (cs, M.insert n2 (AndClause (i1 : lhs) rhs) m)
            _ -> error "found non-and clause"
        (OrNode _, InstanceNode i2) -> (cs, updateOrRhs m n1 e (RhsInstance i2))
        (OrNode _, QueryNode q2) -> (cs, updateOrRhs m n1 e (RhsQuery q2))
        (InstanceNode i1, OrNode _) ->
          case M.lookup n2 m of
            Nothing -> (cs, M.insert n2 (OrClause (Just i1) []) m)
            Just (OrClause _ rhs) -> (cs, M.insert n2 (OrClause (Just i1) rhs) m)
            _ -> error "found non-or clause"
        (_, FoldedNode _) -> (cs, m)
        (_, _) -> error ("found invalid connection " ++ show l1 ++ " -> " ++ show l2)

    -- | Update (or create) the entry for the `and` node by setting the RHS.
    updateAndRhs m n e r =
      case M.lookup n m of
        Nothing -> M.insert n (AndClause [] (Just (e, r))) m
        Just (AndClause lhs _) -> M.insert n (AndClause lhs (Just (e, r))) m
        _ -> error "found non-and clause"

    -- | Update (or create) the entry for the `or` node by augmenting the RHS.
    updateOrRhs m n e r =
      case M.lookup n m of
        Nothing -> M.insert n (OrClause Nothing [(e, r)]) m
        Just (OrClause lhs rhs) -> M.insert n (OrClause lhs ((e, r) : rhs)) m
        _ -> error "found non-or clause"

    chcFromState :: ChcState -> [Chc]
    chcFromState (rs, m) =
      map (\(LinClause i e rhs) -> lin i e rhs) rs ++ concatMap complex (M.elems m)

    -- | Construct a linear Horn Clause.
    lin :: Instance -> ImplGrEdge -> EntryRhs -> Chc
    lin i1 (ImplGrEdge f m) r =
      let r' = subst m r
      in case r' of
        RhsInstance i2 -> Rule [instanceApp i1] f (instanceApp i2)
        RhsQuery q -> Query [instanceApp i1] f q

    -- | A finished complex entry corresponds to some set of Horn Clauses.
    complex :: ComplexClauseEntry -> [Chc]
    complex = \case
      (AndClause is (Just (ImplGrEdge f m, r))) ->
        let r' = subst m r
        in case r' of
          RhsInstance i' -> [Rule (map instanceApp is) f (instanceApp i')]
          RhsQuery q -> [Query (map instanceApp is) f q]
      (OrClause (Just i) outs) -> map (uncurry (lin i)) outs
      _ -> error "incomplete complex clause"

    -- | Convert an instance into an applied function.
    instanceApp :: Instance -> App
    instanceApp i =
      let vs = i ^. variables
          name = "r" ++ intercalate "_" (map show (i ^. identity ++ [i ^. instanceId]))
          t = curryType (map typeOf vs) T.Bool
      in App (Free name t) vs

