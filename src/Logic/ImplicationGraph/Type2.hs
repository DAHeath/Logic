{-# LANGUAGE DeriveDataTypeable, TypeFamilies, TemplateHaskell #-}
module Logic.ImplicationGraph.Type2 where

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Loops (orM, anyM)

import           Data.Data
import           Data.Ord.Graph (Graph)
import qualified Data.Ord.Graph as G
import qualified Data.Ord.Graph.Extras as G
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (mapMaybe, maybeToList, fromJust)
import           Data.List.Split (splitOn)

import           Logic.Formula
import           Logic.Model
import           Logic.Chc
import           Logic.Var
import           Logic.Solver.Z3

import           Text.PrettyPrint.HughesPJClass
import           Text.Read (readMaybe)

data Inst idx
  = BaseInst [idx] [Var] Form
  | AndInst [idx] (Inst idx)
  | OrInst [[idx]] (Inst idx)
  deriving (Show, Read, Eq, Ord, Data)

instForm :: Inst idx -> Form
instForm = \case
  BaseInst _ _ f -> f
  AndInst _ i -> instForm i
  OrInst _ i -> instForm i

data Vert idx
  = InstanceV (Inst idx)
  | QueryV Form
  | FoldedV idx
  deriving (Show, Read, Eq, Ord, Data)
makePrisms ''Vert

data Edge = Edge Form (Map Var Var)
  deriving (Show, Read, Eq, Ord, Data)

instance Pretty Edge where
  pPrint (Edge f m) = pPrint f <+> pPrint (M.toList m)

instance Pretty idx => Pretty (Vert idx) where
  pPrint = \case
    InstanceV i -> pPrint i
    QueryV f -> pPrint f
    FoldedV idx -> text "FOLD" <+> pPrint idx

instance Pretty idx => Pretty (Inst idx) where
  pPrint = \case
    BaseInst _ vs f -> pPrint vs <+> pPrint f
    AndInst idxs inner -> text "and" <+> pPrint idxs <+> pPrint inner
    OrInst idxs inner -> text "or" <+> pPrint idxs <+> pPrint inner

class (Show a, Ord a, Data a) => Idx a where
  type BaseIdx a
  baseIdx :: Lens' a (BaseIdx a)
  toPrefix :: a -> String
  fromPrefix :: String -> Maybe a
  inst :: Lens' a Integer

match :: (Idx a, Eq (BaseIdx a)) => a -> a -> Bool
match x y = x ^. baseIdx == y ^. baseIdx

data LinIdx = LinIdx { _linIden :: Integer, _linInst :: Integer }
  deriving (Show, Read, Eq, Ord, Data)
makeLenses ''LinIdx

instance Idx LinIdx where
  type BaseIdx LinIdx = Integer
  baseIdx = linIden
  toPrefix (LinIdx iden i) = show iden ++ "_" ++ show i
  fromPrefix s = case splitOn "_" s of
      [iden, i] -> LinIdx <$> readMaybe iden <*> readMaybe i
      _ -> Nothing
  inst = linInst

instance Pretty LinIdx where
  pPrint (LinIdx iden i) = pPrint iden <+> pPrint i

type ImplGr idx = Graph idx Edge (Vert idx)

-- | Check whether the vertex labels in the graph form an inductive relationship.
isInductive :: (Eq (BaseIdx idx), Idx idx, MonadIO m) => idx -> ImplGr idx -> m Bool
isInductive start g = evalStateT (ind start) M.empty
  where
    ind i = maybe (computeInd i) return . M.lookup i =<< get

    computeInd i =
      (ix i <.=) =<< maybe (return False) (\case
        FoldedV _ -> return False
        QueryV _ -> return True
        InstanceV ins -> instInd i ins) (g ^. at i)

    instInd i = \case
      BaseInst _ _ f ->
        orM [ return $ f == LBool True
            , anyM (entails f) (descendantInstanceVs i)
            , allInd (G.successors i g)
            ]
      AndInst _ ins -> instInd i ins
      OrInst is _ -> or <$> mapM allInd is

    allInd is = and <$> mapM ind is

    descendantInstanceVs i =
      G.descendants g i
        & filter (match i)
        & mapMaybe (\i' -> instForm <$> (g ^? ix i' . _InstanceV))

-- | Convert the graph into a system of Constrained Horn Clauses.
implGrChc :: Idx idx => ImplGr idx -> [Chc]
implGrChc g = concatMap idxRules (G.idxs g)
  where
    idxApp i = instApp i <$> g ^? ix i . _InstanceV

    instApp i = \case
      BaseInst _ vs _ -> mkApp ('r' : toPrefix i) vs
      OrInst _ ins -> instApp i ins
      AndInst _ ins -> instApp i ins

    idxRules i = maybe [] (\case
      InstanceV ins -> instRules i ins
      QueryV f -> queries i f
      FoldedV _ -> []) (g ^? ix i)

    queries i f =
      mapMaybe (\(i', Edge e mvs) -> do
        lhs <- idxApp i'
        let rhs = subst mvs f
        return (Query [lhs] e rhs)) (g ^@.. G.iedgesTo i)

    instRules i ins = case ins of
      BaseInst is _ _ ->
        mapMaybe (\(i', Edge f mvs) -> do
          lhs <- idxApp i'
          rhs <- subst mvs <$> idxApp i
          return (Rule [lhs] f rhs)) (relevantIncoming i is)
      AndInst is ins' ->
        let (ixs, es) = unzip (relevantIncoming i is)
            (fs, ms) = unzip (map (\(Edge f m) -> (f, m)) es)
        in maybeToList (do
          lhs <- mapM idxApp ixs
          rhs <- subst (M.unions ms) (idxApp i)
          return (Rule lhs (manyAnd fs) rhs)) ++ instRules i ins'
      OrInst _ ins' -> instRules i ins'

    relevantIncoming i is = g ^@.. G.iedgesTo i . indices (`elem` is)

-- | Interpolate the facts in the graph using CHC solving to label the vertices
-- with fresh definitions.
interpolate :: (MonadIO m, Idx idx) => ImplGr idx -> m (Either Model (ImplGr idx))
interpolate g = do
  let chc = implGrChc g
  solveChc chc >>= \case
    Left m -> return (Left m)
    Right m -> return (Right $ applyModel m g)

-- | Replace the fact at each vertex in the graph by the fact in the model.
applyModel :: Idx idx => Model -> ImplGr idx -> ImplGr idx
applyModel m = G.imapVerts applyVert
  where
    applyVert i = \case
      InstanceV inst ->
        let fact = M.findWithDefault (LBool True) i m'
        in InstanceV (replaceFact fact inst)
      n -> n

    replaceFact f = \case
      BaseInst is vs _ -> BaseInst is vs f
      AndInst is ins -> AndInst is (replaceFact f ins)
      OrInst is ins -> OrInst is (replaceFact f ins)

    m' = M.mapKeys (interpretName . varName) $
           M.filterWithKey (\k _ -> head (varName k) == 'r') (getModel m)
      where
        interpretName ('r':rest) = fromJust $ fromPrefix rest
        interpretName _ = undefined

emptyImplGr :: ImplGr ix
emptyImplGr = G.empty

emptyInst :: Idx idx => idx -> [Var] -> ImplGr idx -> ImplGr idx
emptyInst i vs = G.addVert i (InstanceV (BaseInst [] vs (LBool True)))

query :: Idx idx => idx -> Form -> ImplGr idx -> ImplGr idx
query i f = G.addVert i (QueryV f)

edge :: Idx idx => idx -> idx -> Form -> Map Var Var -> ImplGr idx -> ImplGr idx
edge i1 i2 f m g = G.addEdge i1 i2 (Edge f m) (g & ix i2 . _InstanceV %~ addInc i1)
  where
    addInc i = \case
      BaseInst is vs f -> BaseInst (i:is) vs f
      AndInst is ins -> AndInst is (addInc i ins)
      OrInst is ins -> OrInst is (addInc i ins)

connAnd :: Idx idx => [idx] -> idx -> Form -> Map Var Var -> ImplGr idx -> ImplGr idx
connAnd is i f m g =
  foldr (\(i', f', m') -> G.addEdge i' i (Edge f' m'))
        (g & ix i . _InstanceV %~ AndInst is)
        (zip3 is (f:repeat (LBool True)) (m:repeat M.empty))

connOr :: Idx idx => [[idx]] -> idx -> ImplGr idx -> ImplGr idx
connOr is i = ix i . _InstanceV %~ OrInst is

test = G.fromLists
  [ (0, 'a')
  , (1, 'b')
  , (2, 'c')
  , (3, 'd')
  ]
  [ (0, 1, 'w')
  , (1, 2, 'x')
  , (2, 3, 'y')
  , (3, 1, 'z')
  ]
