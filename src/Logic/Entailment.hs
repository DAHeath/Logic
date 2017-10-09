{-# LANGUAGE TemplateHaskell #-}
module Logic.Entailment where

import           Control.Lens hiding (Context)
import           Control.Monad.State

import           Data.Data (Data)
import           Data.Graph.Inductive.Basic
import           Data.Graph.Inductive.Graph hiding ((&))
import           Data.Graph.Inductive.PatriciaTree
import           Data.Graph.Inductive.Extras
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (mapMaybe, fromJust)
import           Data.List (intercalate)
import           Data.List.Split (splitOn)
import           Data.Foldable (foldrM)

import           Logic.Type as T
import           Logic.Var
import           Logic.Formula
import           Logic.Solver.Z3
import           Logic.Chc
import           Logic.Model

import           Text.PrettyPrint.HughesPJClass as PP

type InstanceId = Int
type Lbl = Int

data Inductive
  = NotInductive
  | UnknownIfInductive
  | InductiveSucc
  | InductiveFalse
  | InductiveBy InstanceId
  deriving (Show, Read, Eq, Ord, Data)

instance Pretty Inductive where
  pPrint = \case
    NotInductive -> text "NOT-IND"
    UnknownIfInductive -> text "UNK-IND"
    InductiveSucc -> text "IND-BY-SUCC"
    InductiveFalse -> text "IND-BY-FALSE"
    InductiveBy i -> text "IND-BY-ENT" <+> pPrint i

data Instance = Instance
  { _identity :: [Lbl]
  , _instanceId :: InstanceId
  , _variables :: [Var]
  , _formula :: Form
  , _inductive :: Inductive
  } deriving (Show, Read, Eq, Ord, Data)

instance Pretty Instance where
  pPrint (Instance ids ins vs f ind) =
    hsep [pPrint ids, pPrint ins, pPrint vs, pPrint f, pPrint ind]

mkInstance :: [Lbl] -> [Var] -> Instance
mkInstance ids vs = Instance ids 0 vs (LBool True) UnknownIfInductive

makeLenses ''Instance

data EntailmentNode
  = AndNode
  | OrNode
  | InstanceNode Instance
  | QueryNode Form
  deriving (Show, Read, Eq, Ord, Data)

instance Pretty EntailmentNode where
  pPrint = \case
    AndNode -> text "AND"
    OrNode -> text "OR"
    InstanceNode i -> pPrint i
    QueryNode f -> pPrint f

data EntailmentEdge = EntailmentEdge Form (Map Var Var)
  deriving (Show, Read, Eq, Ord, Data)

instance Pretty EntailmentEdge where
  pPrint (EntailmentEdge f m) = pPrint f <+> pPrint (M.toList m)

type Entailment = Gr EntailmentNode EntailmentEdge

backEdges :: [Int] -> Entailment -> [LEdge EntailmentEdge]
backEdges dims g = S.toList $ ufold (\c s -> s `S.union` ctxSet c) S.empty g
  where
    ctxSet :: Context EntailmentNode EntailmentEdge -> Set (LEdge EntailmentEdge)
    ctxSet (bef, n, here, aft) =
      let befSets = mapMaybe (\(e, n') -> do
                                l <- lab g n'
                                return (backEdgeSet e (n', l) (n, here))) bef
          aftSets = mapMaybe (\(e, n') -> do
                                l <- lab g n'
                                return (backEdgeSet e (n, here) (n', l))) aft
      in S.unions (befSets ++ aftSets)

    backEdgeSet :: EntailmentEdge
                -> LNode EntailmentNode
                -> LNode EntailmentNode
                -> Set (LEdge EntailmentEdge)
    backEdgeSet e (n1, l1) (n2, l2) = case (l1, l2) of
      (InstanceNode l1', InstanceNode l2') ->
        if (l2' ^. identity) `leq` (l1' ^. identity)
        then S.singleton (n1, n2, e)
        else S.empty
      _ -> S.empty

    leq :: [Lbl] -> [Lbl] -> Bool
    leq x y = loc dims x <= loc dims y

loc :: [Int] -> [Lbl] -> Int
loc dims = sum . zipWith dimension [0..]
  where
    dimension dim i = i * product (take dim dims)

-- unfolding allBes bes g =
--   let g' = evalState (foldrM unfold g bes) M.empty
--       g'' = efilter (`notElem` allBes) g'
--   in treeFrom 0 g''

data EntryRhs
  = RhsInstance Instance
  | RhsQuery Form
  deriving (Show, Read, Eq, Ord, Data)

data ComplexClauseEntry
  = AndClause [Instance] (Maybe (EntailmentEdge, EntryRhs))
  | OrClause (Maybe Instance) [(EntailmentEdge, EntryRhs)]
  deriving (Show, Read, Eq, Ord, Data)

data LinClause = LinClause Instance EntailmentEdge EntryRhs
  deriving (Show, Read, Eq, Ord, Data)

type ChcState = ([LinClause], Map Node ComplexClauseEntry)

-- | Convert an instance into an applied function.
instanceApp :: Instance -> App
instanceApp i =
  let vs = i ^. variables
      name = "r" ++ intercalate "_" (map show (i ^. identity ++ [i ^. instanceId]))
      t = curryType (map typeOf vs) T.Bool
  in App (Free name t) vs

-- | Convert an entailment graph into a constrained Horn Clause system.
entailmentChc :: Entailment -> [Chc]
entailmentChc g = chcFromState $ ufold ctx ([], M.empty) g
  where
    -- | Given the context for some node, update the state by augmenting new
    -- linear Horn Clauses and adding new or modifiying existing complex clauses.
    ctx (bef, n, here, aft) st1 =
      let st2 = foldr connect st1 (zip3 (map (node . snd) bef) (map fst bef) (repeat (n, here)))
          st3 = foldr connect st2 (zip3 (repeat (n, here)) (map fst aft) (map (node . snd) aft))
      in st3

    node :: Node -> (Node, EntailmentNode)
    node n = (n, fromJust $ lab g n)

    -- | Each edge in the entailment represents either a linear Horn Clause
    -- (between instance and instance nodes or instance and query nodes) or a
    -- portion of some complex relationship.
    connect :: ((Node, EntailmentNode), EntailmentEdge, (Node, EntailmentNode))
            -> ChcState -> ChcState
    connect ((n1, l1), e, (n2, l2)) (cs, m) =
      case (l1, l2) of
        (InstanceNode i1, InstanceNode i2) -> (LinClause i1 e (RhsInstance i2) : cs, m)
        (InstanceNode i1, QueryNode q2) -> (LinClause i1 e (RhsQuery q2) : cs, m)
        (AndNode, InstanceNode i2) -> (cs, updateAndRhs m n1 e (RhsInstance i2))
        (AndNode, QueryNode q2) -> (cs, updateAndRhs m n1 e (RhsQuery q2))
        (InstanceNode i1, AndNode) ->
          case M.lookup n2 m of
            Nothing -> (cs, M.insert n2 (AndClause [i1] Nothing) m)
            Just (AndClause lhs rhs) -> (cs, M.insert n2 (AndClause (i1 : lhs) rhs) m)
            _ -> error "found non-and clause"
        (OrNode, InstanceNode i2) -> (cs, updateOrRhs m n1 e (RhsInstance i2))
        (OrNode, QueryNode q2) -> (cs, updateOrRhs m n1 e (RhsQuery q2))
        (InstanceNode i1, OrNode) ->
          case M.lookup n2 m of
            Nothing -> (cs, M.insert n2 (OrClause (Just i1) []) m)
            Just (OrClause _ rhs) -> (cs, M.insert n2 (OrClause (Just i1) rhs) m)
            _ -> error "found non-or clause"
        (_, _) -> error "found invalid connection"

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
    lin :: Instance -> EntailmentEdge -> EntryRhs -> Chc
    lin i1 (EntailmentEdge f m) r =
      let r' = subst m r
      in case r' of
        RhsInstance i2 -> Rule [instanceApp i1] f (instanceApp i2)
        RhsQuery q -> Query [instanceApp i1] f q

    -- | A finished complex entry corresponds to some set of Horn Clauses.
    complex :: ComplexClauseEntry -> [Chc]
    complex = \case
      (AndClause is (Just (EntailmentEdge f m, r))) ->
        let r' = subst m r
        in case r' of
          RhsInstance i' -> [Rule (map instanceApp is) f (instanceApp i')]
          RhsQuery q -> [Query (map instanceApp is) f q]
      (OrClause (Just i) outs) -> map (uncurry (lin i)) outs
      _ -> error "incomplete complex clause"

interpretModel :: Model -> Map ([Lbl], InstanceId) Form
interpretModel (Model m) = M.mapKeys (interpretName . varName) m
  where
    interpretName :: Name -> ([Lbl], InstanceId)
    interpretName ('r':rest) =
      let ls = map read (splitOn "_" rest)
      in (init ls, last ls)
    interpretName n = ([], -1)

applyModel :: Model -> Entailment -> Entailment
applyModel m = nmap node
  where
    node = \case
      InstanceNode i ->
        let fact = M.findWithDefault (LBool True) (i ^. identity, i ^. instanceId) mod
        in InstanceNode (i & formula .~ fact)
      n -> n

    mod = interpretModel m

solve :: Entailment -> IO (Either Model Entailment)
solve g = do
  let sys = entailmentChc g
  sol <- solveChc sys
  case sol of
    Left m -> return (Left m)
    Right m -> return (Right $ applyModel m g)

-- isInductive :: Entailment -> Bool
-- isInductive = 
