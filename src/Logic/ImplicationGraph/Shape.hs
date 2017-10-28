{-# LANGUAGE TypeFamilies, QuasiQuotes, LambdaCase, FlexibleContexts, DeriveDataTypeable, ConstraintKinds #-}
module Logic.ImplicationGraph.Shape where

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Reader
import           Control.Arrow (first)

import           Data.Data (Data)
import           Data.Foldable (foldrM)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Optic.Graph (Graph)
import qualified Data.Optic.Graph as G
import qualified Data.Optic.Graph.Extras as G
import           Data.Maybe (fromMaybe)
import           Data.Monoid (Any)
import           Data.List.Split (splitOn)

import qualified Logic.Type as T
import           Logic.Formula
import           Logic.Formula.Parser
import           Logic.Var
import           Logic.ImplicationGraph.Solve
import           Logic.ImplicationGraph.Type
import           Logic.ImplicationGraph.Interpolate
import           Logic.ImplicationGraph.Induction

import           Text.PrettyPrint.HughesPJClass (prettyShow, Pretty, pPrint, (<+>))

data SLbl
  = MainLine Lbl
  | Branch Lbl InstanceId Lbl
  deriving (Show, Read, Eq, Data)

instance Ord SLbl where
  compare x y = compare (listOf x) (listOf y)
    where
      listOf (MainLine l) = [l]
      listOf (Branch a b c) = [c, a, b]

instance LblLike SLbl where
  type Base SLbl = (Int, Int)

  toBase (MainLine i) = (i, i)
  toBase (Branch i1 _ i2) = (i1, i2)

  match x y = toBase x == toBase y

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


noBackedges :: SGr -> SGr
noBackedges g =
  foldr (\(i, _) -> uncurry G.delEdge i) g (backEdges' g)

edgesWithForm :: Getting Any Form a -> Graph i ImplGrEdge v -> [((i, i), ImplGrEdge)]
edgesWithForm p g =
  filter (\(_, ImplGrEdge f _) -> any (has p) $ universe f) (g ^@.. G.iallEdges)

forwardEdgesWithForm :: Getting Any Form a -> SGr -> [((SNode, SNode), ImplGrEdge)]
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
storeElimination orig = foldrM elim orig (forwardEdgesWithForm _Store orig)
  where
    elim :: Shape m => ((SNode, SNode), ImplGrEdge) -> SGr -> m SGr
    elim ((n1, n2), ImplGrEdge f m) g =
      let (f', _) = removeStores f
          g' = G.addEdge n1 n2 (ImplGrEdge f' m) g
      in if isMainLine n1 && isMainLine n2 then
           let swpPos2 = G.reached n2 g'
                 & G.filterIdxs isMainLine
                 & G.mapIdxs (branch n1)

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
    addStore (((iden, _), _), ImplGrEdge f _) m =
      let (_, (obj, val)) = removeStores f
      in M.insert iden (obj, val) m

isMainLine :: SNode -> Bool
isMainLine (MainLine{}, _) = True
isMainLine _ = False

storeId :: SNode -> SNode
storeId (Branch _ _ sId, sInst) = (MainLine sId, sInst)

toMainLine :: SNode -> SNode
toMainLine (Branch iden inst _, _) = (MainLine iden, inst)
toMainLine sn = sn

branch :: SNode -> SNode -> SNode
branch (MainLine loc1, inst1) (MainLine loc2, inst2) = (Branch loc2 inst2 loc1, inst1)

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
  InstanceNode (vs, f) -> InstanceNode (vs ++ [map (storedVar no) svs], f)
  n -> n

selectElimination :: Shape m => SGr -> m SGr
selectElimination orig = foldrM elim orig (forwardEdgesWithForm _Select orig)
  where
    elim ((n1, n2), ImplGrEdge f m) g =
      let (f', (obj, val)) = removeSelects f
      in if isMainLine n1 && isMainLine n2
         then return (G.delEdge n1 n2 g)
         else do
           matchE <- matchNodeForm obj val n1 (ImplGrEdge f' m)

           g' <- addAndNode [toMainLine n1, n1] (toMainLine n2) matchE g

           g'' <- crossEdges obj val n1 n2 (crossCandidates n1) (ImplGrEdge f' m) g'
           return $ G.addEdge n1 n2 matchE g''

    selects = selectLocs orig
    crossCandidates (Branch iden inst sIden, sInst)
      = concatMap (\can@(Branch iden' inst' sIden', sInst') ->
          if sIden == sIden' && sInst == sInst' then []
          else [can | iden == iden' && inst == inst']) selects

crossEdges :: Shape m => Form -> Form -> SNode -> SNode -> [SNode] -> ImplGrEdge -> SGr -> m SGr
crossEdges obj val n1 tar cans e g =
  foldrM (\n2 g' ->
    if storeId n1 == n2 then return g
    else do
      e' <- matchNodeForm obj val n2 e
      crossEdge n1 n2 tar e' g') g cans

matchNodeForm :: Shape m => Form -> Form -> SNode -> ImplGrEdge -> m ImplGrEdge
matchNodeForm obj val n@(Branch _ _ iden, _) (ImplGrEdge f m) = do
  (stobj, stval) <- M.findWithDefault (LBool True, LBool True) iden <$> ask
  let stobj' = storedForm n stobj
  let stval' = storedForm n stval
  let mtch = [form|$obj:Int = $stobj':Int && $val:Int = $stval':Int|]
  return $ ImplGrEdge (mkAnd mtch f) m

crossEdge :: Shape m => SNode -> SNode -> SNode -> ImplGrEdge -> SGr -> m SGr
crossEdge n1 n2 = addAndNode [n1, n2]

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

shapeStep :: Shape m => Set SNode -> SGr -> m (Either (Set SNode, SGr) SGr)
shapeStep alreadyInd g = do
  g' <- G.reached (MainLine 0, 0) <$> foldrM unfold g (backEdges' g)
  -- g'' <- G.filterIdxs (`notElem` alreadyInd) <$> storeUnfold g'
  g'' <- storeUnfold g'
  let reach = G.reached (MainLine 0, 0) g''
  let toEval = G.filterIdxs (\i -> fst i /= MainLine 3) $ G.filterIdxs (`elem` G.idxs reach) g''
  liftIO $ G.display "toEval" toEval
  sol <- liftIO (interpolate toEval)
  case sol of
    Left m -> do
      liftIO $ G.display "error" toEval
      error (prettyShow m)
    Right interped -> do
      ind <- liftIO $ isInductive (MainLine 0, 0) interped
      case ind of
        Right done -> do
          liftIO $ putStrLn "inductive"
          return (Right done)
        Left indS -> do
          liftIO $ putStrLn "not inductive"
          return (Left (alreadyInd `S.union` indS, g'))

loop :: Shape m => Int -> Set SNode -> SGr -> m SGr
loop 0 _ g = storeUnfold g
loop n alreadyInd g =
  do
    liftIO $ putStrLn "loop!"
    sol <- shapeStep alreadyInd g
    case sol of
      Left (ind', g') -> loop (n-1) ind' g'
      Right g' -> storeUnfold g'

shape :: Int -> ImplGr -> IO (Map (Int, Int) Form)
shape i g = do
  let g' = gNoFieldVars g
  let solSt = mapSolveState MainLine $ emptySolveState g'

  sol <- evalStateT (
        runReaderT (loop i S.empty (toShapeGr g')) (storeInfo g')
        ) solSt
  print (M.map prettyShow $ collectAnswer sol)
  G.display "elim2" sol
  return (collectAnswer sol)
