{-# LANGUAGE QuasiQuotes, LambdaCase, FlexibleContexts, DeriveDataTypeable, ConstraintKinds #-}

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Arrow (first)

import           Data.Data (Data)
import qualified Data.Ord.Graph.Extras as G
import qualified Data.Ord.Graph as G
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.List (intercalate)
import           Data.List.Split (splitOn)
import           Data.Maybe
import           Data.Monoid (Any)
import           Data.Foldable

import qualified Logic.Type as T
import           Logic.Formula
import           Logic.Formula.Parser
import           Logic.Var
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Type
import           Logic.ImplicationGraph.Interpolate
import           Logic.ImplicationGraph.Induction
import           Text.PrettyPrint.HughesPJClass (prettyShow, Pretty, pPrint, (<+>))

import Debug.Trace

h, h', t, t', i, i', c, c', n, next, next' :: Var
h  = Free "h"  T.Int
h' = Free "h'" T.Int
t  = Free "t"  T.Int
t' = Free "t'" T.Int
i  = Free "i"  T.Int
i' = Free "i'" T.Int
c  = Free "c"  T.Int
c' = Free "c'" T.Int
n  = Free "n" T.Int
next  = Free "next" (T.Array T.Int T.Int)
next' = Free "next" (T.Array T.Int T.Int)

-- example :: Comm
-- example = Seq
--   (Ass h (Expr [form|1|])) $ Seq
--   (Ass t (Expr (V h))) $ Seq
--   (Ass i (Expr [form|2|])) $ Seq
--   (Ass c (Expr [form|0|])) $ Seq
--   (Loop [form|c:Int < n:Int|] $ Seq
--     (Save "next" (V t) (V i)) $ Seq
--     (Ass t (Expr (V i)))
--     (Ass i (Expr [form|i:Int + 1|]))) $ Seq
--   (Ass c (Expr [form|0|]))
--   (Loop [form|c:Int < n:Int|]
--     (Ass h (Load "next" (V h))))

data SLbl
  = MainLine Lbl
  | Branch Lbl InstanceId Lbl
  deriving (Show, Read, Eq, Data)

instance Ord SLbl where
  compare x y = compare (listOf x) (listOf y)
    where
      listOf (MainLine l) = [l]
      listOf (Branch a b c) = [a, b, c]

instance LblLike SLbl where
  match (MainLine i) (MainLine i') = i == i'
  match (Branch i1 _ i2) (Branch i1' _ i2') = i1 == i1' && i2 == i2'
  match _ _ = False

  toPrefix (MainLine i) = show i
  toPrefix (Branch i1 ins1 i2) = show i1 ++ "_" ++ show ins1 ++ "_" ++ show i2

  fromPrefix s =
    case splitOn "_" s of
      [i, inst] -> [(MainLine (read i), "_" ++ inst)]
      [i1, inst1, i2, inst2] -> [(Branch (read i1) (read inst1) (read i2), "_" ++ inst2)]
      _ -> []

instance Pretty SLbl where
  pPrint (MainLine l) = pPrint l
  pPrint (Branch a b c) = pPrint a <+> pPrint b <+> pPrint c

g :: ImplGr
g =

  G.fromLists
    [ ((0, 0), InstanceNode $ emptyInstance [])
    , ((1, 0), InstanceNode $ emptyInstance [h, t, i, c, n, next])
    , ((2, 0), InstanceNode $ emptyInstance [h, t, c, n, next])
    , ((3, 0), QueryNode [form|h:Int = t:Int|])
    ]
    [ ((0, 0), (1, 0),
      ImplGrEdge [form| h:Int = 1
                     && t:Int = 1
                     && i:Int = 2
                     && c:Int = 0|]
                 M.empty)
    , ((1, 0), (1, 0),
      ImplGrEdge [form| c:Int < n:Int
                     && next':Arr{Int,Int} = store next:Arr{Int,Int} t:Int i:Int
                     && t':Int = i:Int
                     && i':Int = i:Int + 1
                     && c':Int = c:Int + 1|]
                 (M.fromList [(next, next'), (t, t'), (i, i'), (c, c')]))
    , ((1, 0), (2, 0),
      ImplGrEdge [form| c:Int >= n:Int && c':Int = 0|]
                 (M.singleton c c'))
    , ((2, 0), (2, 0),
      ImplGrEdge [form| c:Int < n:Int
                     && c':Int = c:Int + 1
                     && h':Int = select next:Arr{Int,Int} h:Int |]
                 (M.fromList [(h, h'), (c, c')]))
    , ((2, 0), (3, 0),
      ImplGrEdge [form|c:Int >= n:Int|] M.empty)
    ]

noBackedges :: SGr -> SGr
noBackedges g =
  foldr (\(i, _) -> uncurry G.delEdge i) g (backEdges' g)

-- edgesWithForm :: Getting Any Form a -> ImplGr -> [((Node, Node), ImplGrEdge)]
edgesWithForm p g =
  filter (\(_, ImplGrEdge f _) -> any (has p) $ universe f) (g ^@.. G.iallEdges)

-- forwardEdgesWithForm :: Getting Any Form a -> ImplGr -> [((Node, Node), ImplGrEdge)]
forwardEdgesWithForm p g = edgesWithForm p (noBackedges g)

removeStores :: Form -> (Form, (Form, Form))
removeStores f = runState (rewriteM (\case
  (Eql _ :@ (Store _ _ :@ _ :@ obj :@ val) :@ _) -> put (obj, val) >> return (Just (LBool True))
  (Eql _ :@ _ :@ (Store _ _ :@ _ :@ obj :@ val)) -> put (obj, val) >> return (Just (LBool True))
  _       -> return Nothing) f) (LBool True, LBool True)

removeSelects :: Form -> (Form, (Form, Form))
removeSelects f = runState (rewriteM (\case
  (Eql _ :@ (Select _ _ :@ _ :@ obj) :@ val) -> put (obj, val) >> return (Just (LBool True))
  (Eql _ :@ val :@ (Select _ _ :@ _ :@ obj)) -> put (obj, val) >> return (Just (LBool True))
  _       -> return Nothing) f) (LBool True, LBool True)

type StoreInfo = Map Lbl (Form, Form)
type SGr = ImplGr' SLbl
type SNode = Node' SLbl
type Shape m = (MonadReader StoreInfo m, MonadState (SolveState' SLbl) m, MonadIO m)

toShapeGr :: ImplGr -> SGr
toShapeGr = G.mapVerts (\case
  FoldedNode (iden, inst) -> FoldedNode (MainLine iden, inst)
  AndNode -> AndNode
  OrInputNode -> OrInputNode
  OrOutputNode -> OrOutputNode
  InstanceNode i -> InstanceNode i
  QueryNode f -> QueryNode f) . G.mapIdxs (first MainLine)

storeElimination :: Shape m => SGr -> m SGr
storeElimination g = foldrM elim g (forwardEdgesWithForm _Store g)
  where
    elim :: Shape m => ((SNode, SNode), ImplGrEdge) -> SGr -> m SGr
    elim ((n1, n2), ImplGrEdge f m) g =
      let (f', (obj, val)) = removeStores f
          g' = G.addEdge n1 n2 (ImplGrEdge f' m) g
      in if isMainLine n1 && isMainLine n2 then
           let swpPos2 = G.reached n2 g' & G.filterIdxs isMainLine & G.mapIdxs (branch n1)
               vs = fromMaybe [] (g' ^? ix n1 . _InstanceNode . _1 . ix 0)
               loc = branch n1 n2
               swpPos2' = G.mapVerts (copyStoredVars loc vs) swpPos2
               copies = manyAnd $ map (\v -> mkEql (T.typeOf v) (V v) (V (storedVar loc v))) vs
           in
             return $ G.addEdge n1 (branch n1 n2) (ImplGrEdge (mkAnd copies f') m) (g' `G.union` swpPos2')
        else return g'

storeInfo :: ImplGr -> Map Lbl (Form, Form)
storeInfo g = foldr addStore M.empty (edgesWithForm _Store g)
  where
    addStore (((iden, inst), _), ImplGrEdge f _) m =
      let (_, (obj, val)) = removeStores f
      in M.insert iden (obj, val) m

isMainLine :: SNode -> Bool
isMainLine (MainLine{}, _) = True
isMainLine _ = False

storeId :: SNode -> SNode
storeId (Branch sId sInst _, _) = (MainLine sId, sInst)

toMainLine :: SNode -> SNode
toMainLine (Branch _ _ id, inst) = (MainLine id, inst)
toMainLine sn = sn

branch :: SNode -> SNode -> SNode
branch (MainLine loc1, inst1) (MainLine loc2, inst2) = (Branch loc1 inst1 loc2, inst2)

selectLocs :: SGr -> [SNode]
selectLocs g = filter (not . isMainLine) $ map (fst . fst) (forwardEdgesWithForm _Select g)

storedForm :: SNode -> Form -> Form
storedForm n = transform (\case
  V v -> V $ storedVar n v
  f -> f)

storedVar :: SNode -> Var -> Var
storedVar no = \case
  Free n t -> Free (prefix ++ n) t
  Bound n t -> Free (prefix ++ show n) t
  where
    prefix = "s" ++ nodePrefix (storeId no)

copyStoredVars :: SNode -> [Var] -> ImplGrNode' SLbl -> ImplGrNode' SLbl
copyStoredVars no svs = \case
  InstanceNode (vs, f) -> InstanceNode (map (storedVar no) svs:vs, f)
  n -> n

selectElimination :: Shape m => SGr -> m SGr
selectElimination g = foldrM elim g (forwardEdgesWithForm _Select g)
  where
    elim ((n1, n2), ImplGrEdge f m) g =
      let (f', (obj, val)) = removeSelects f
      in if isMainLine n1 && isMainLine n2
         then return (G.delEdge n1 n2 g)
         else do
           let (Branch iden inst _, _) = n1
           matchE <- matchNodeForm obj val n1 (ImplGrEdge f' m)

           g' <- addAndNode [toMainLine n1, n1] (toMainLine n2) matchE g

           g'' <- crossEdges obj val n1 n2 (crossCandidates n1) (ImplGrEdge f' m) g'
           return $ G.addEdge n1 n2 matchE g''

    selects = selectLocs g
    crossCandidates (Branch sIden sInst iden, inst)
      = concatMap (\can@(Branch sIden' sInst' iden', inst') ->
          if sIden == sIden' && sInst == sInst' then []
          else [can | iden == iden' && inst == inst']) selects

matchNodeForm obj val n@(Branch iden _ _, _) (ImplGrEdge f m) = do
  (stobj, stval) <- M.findWithDefault (LBool True, LBool True) iden <$> ask
  let stobj' = storedForm n stobj
  let stval' = storedForm n stval
  let mtch = [form|$obj:Int = $stobj':Int && $val:Int = $stval':Int|]
  return $ ImplGrEdge (mkAnd mtch f) m

crossEdges :: Shape m => Form -> Form -> SNode -> SNode -> [SNode] -> ImplGrEdge -> SGr -> m SGr
crossEdges obj val n1 tar cans e g =
  foldrM (\n2 g ->
    if storeId n1 == n2 then return g
    else do
      e' <- matchNodeForm obj val n2 e
      crossEdge n1 n2 tar e' g) g cans

crossEdge :: Shape m => SNode -> SNode -> SNode -> ImplGrEdge -> SGr -> m SGr
crossEdge n1 n2 = addAndNode [n1, n2]

backEdges' :: SGr -> [((SNode, SNode), ImplGrEdge)]
backEdges' = G.backEdges . withoutModNodes

withoutModNodes :: SGr -> SGr
withoutModNodes =
  G.filterVerts
    (\v -> not (has _AndNode v || has _OrInputNode v || has _OrOutputNode v || has _FoldedNode v))

noFieldVars :: [Var] -> [Var]
noFieldVars = filter (not . has T._Array . T.typeOf)

gNoFieldVars :: ImplGr -> ImplGr
gNoFieldVars = G.mapVerts (\case
  InstanceNode (vs, f) -> InstanceNode (map noFieldVars vs, f)
  n -> n)

storeUnfold :: Shape m => SGr -> m SGr
storeUnfold g = do
  g' <- storeElimination g >>= selectElimination
  foldBackedges (backEdges' g') g'

shapeStep :: Shape m => SGr -> m (Either SGr SGr)
shapeStep g = do
  g' <- foldrM unfold g (backEdges' g)
  g'' <- storeUnfold g'
  let re = G.reached (MainLine 0, 0) g''
  let toEval = G.filterIdxs (`elem` G.idxs re) g''
  sol <- liftIO (interpolate toEval)
  case sol of
    Left m -> error (prettyShow m)
    Right interped -> do
      b <- liftIO $ isInductive (MainLine 0, 0) interped
      if b then
        return (Right interped)
      else do
        liftIO $ putStrLn "not inductive"
        return (Left g')

shape :: Shape m => Int -> SGr -> m SGr
shape 0 g = storeUnfold g
shape n g =
  do
    sol <- shapeStep g
    case sol of
      Left g' -> shape (n-1) g'
      Right g' -> storeUnfold g'

main :: IO ()
main = do
  let g' = gNoFieldVars g
  let solSt = mapSolveState MainLine $ emptySolveState g'

  sol <- evalStateT (
        runReaderT (shape 2 (toShapeGr g')) (storeInfo g')
        ) solSt
  -- putStrLn (prettyShow $ entailmentChc (noBackedges sol))
  G.display "elim2" sol
