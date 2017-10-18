{-# LANGUAGE QuasiQuotes, LambdaCase #-}

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Except

import qualified Data.Ord.Graph.Extras as G
import qualified Data.Ord.Graph as G
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.List (intercalate)
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
import           Text.PrettyPrint.HughesPJClass

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

g :: ImplGr
g =

  G.fromLists
    [ (([0], 0), InstanceNode $ emptyInstance [])
    , (([1], 0), InstanceNode $ emptyInstance [h, t, i, c, n, next])
    , (([2], 0), InstanceNode $ emptyInstance [h, t, c, n, next])
    , (([3], 0), QueryNode [form|h:Int = t:Int|])
    ]
    [ (([0], 0), ([1], 0),
      ImplGrEdge [form| h:Int = 1
                     && t:Int = 1
                     && i:Int = 2
                     && c:Int = 0|]
                 M.empty)
    , (([1], 0), ([1], 0),
      ImplGrEdge [form| c:Int < n:Int
                     && next':Arr{Int,Int} = store next:Arr{Int,Int} t:Int i:Int
                     && t':Int = i:Int
                     && i':Int = i:Int + 1
                     && c':Int = c:Int + 1|]
                 (M.fromList [(next, next'), (t, t'), (i, i'), (c, c')]))
    , (([1], 0), ([2], 0),
      ImplGrEdge [form| c:Int >= n:Int && c':Int = 0|]
                 (M.singleton c c'))
    , (([2], 0), ([2], 0),
      ImplGrEdge [form| c:Int < n:Int
                     && c':Int = c:Int + 1
                     && h':Int = select next:Arr{Int,Int} h:Int |]
                 (M.fromList [(h, h'), (c, c')]))
    , (([2], 0), ([3], 0),
      ImplGrEdge [form|c:Int >= n:Int|] M.empty)
    ]

noBackedges :: ImplGr -> ImplGr
noBackedges g =
  foldr (\(i, _) -> uncurry G.delEdge i) g (backEdges' g)

edgesWithForm :: Getting Any Form a -> ImplGr -> [((Node, Node), ImplGrEdge)]
edgesWithForm p g =
  filter (\(_, ImplGrEdge f _) -> any (has p) $ universe f)
         (noBackedges g ^@.. G.iallEdges)

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

type ShapeState = Map Lbl (Form, Form)

storeElimination :: ImplGr -> StateT ShapeState (StateT SolveState IO) ImplGr
storeElimination g = foldrM elim g (edgesWithForm _Store g)
  where
    elim :: ((Node, Node), ImplGrEdge) -> ImplGr -> StateT ShapeState (StateT SolveState IO) ImplGr
    elim ((n1, n2), ImplGrEdge f m) g =
      let (f', (obj, val)) = removeStores f
          g' = G.addEdge n1 n2 (ImplGrEdge f' m) g
      in if isMainline n1 && isMainline n2 then
           let swpPos2 = G.reached n2 g' & G.filterIdxs isMainline & G.mapIdxs (prod n1)
               vs = fromMaybe [] (g' ^? ix n1 . _InstanceNode . _1 . ix 0)
               loc = prod n1 n2
               swpPos2' = G.mapVerts (copyStoredVars loc vs) swpPos2
               copies = manyAnd $ map (\v -> mkEql (T.typeOf v) (V v) (V (storedVar loc v))) vs
           in do
             modify (M.insert (prod n1 n2) (storedForm loc obj, storedForm loc val))
             return $ G.addEdge n1 (prod n1 n2) (ImplGrEdge (mkAnd copies f') m) (g' `G.union` swpPos2')
        else return g'

    prod (loc1, inst1) (loc2, inst2) = ([head loc1, inst1, head loc2], inst2)
    isMainline n = length (fst n) == 1

nodeToIdxs :: Node -> [Int]
nodeToIdxs (iden, inst) = iden ++ [inst]

storedForm :: Node -> Form -> Form
storedForm n = transform (\case
  V v -> V $ storedVar n v
  f -> f)

storedVar :: Node -> Var -> Var
storedVar no = \case
  Free n t -> Free (prefix ++ n) t
  Bound n t -> Free (prefix ++ show n) t
  where
    prefix = "s" ++ intercalate "_" (map show (nodeToIdxs no)) ++ "/"

copyStoredVars :: Node -> [Var] -> ImplGrNode -> ImplGrNode
copyStoredVars no svs = \case
  InstanceNode (vs, f) -> InstanceNode (map (storedVar no) svs:vs, f)
  n -> n

selectElimination :: ImplGr -> StateT ShapeState (StateT SolveState IO) ImplGr
selectElimination g = foldrM elim g (edgesWithForm _Select g)
  where
    elim :: ((Node, Node), ImplGrEdge) -> ImplGr -> StateT ShapeState (StateT SolveState IO) ImplGr
    elim ((n1, n2), ImplGrEdge f m) g =
      let (f', (obj, val)) = removeSelects f
      in if length (fst n1) == 1 && length (fst n2) == 1
         then return (G.delEdge n1 n2 g)
         else do
           let ([iden, inst, _, _], _) = n1
           mapping <- get
           liftIO $ print mapping
           liftIO $ print n1
           liftIO $ print n2
           (stobj, stval) <- M.findWithDefault (LBool True, LBool True) n1 <$> get
           let mtch = [form|$obj:Int = $stobj:Int && $val:Int = $stval:Int|]
           let matchE = ImplGrEdge (mkAnd mtch f') m
           g' <- lift (addAndNode [simpleNode n1, n1] (simpleNode n2) matchE g)
           g'' <- crossEdges n1 n2 matchE g'
           return $ G.addEdge n1 n2 matchE g''

    simpleNode ([l1, i1, l2], i2) = ([l2], i2)

crossEdges :: Node -> Node -> ImplGrEdge -> ImplGr -> StateT ShapeState (StateT SolveState IO) ImplGr
crossEdges n1 tar e g = do
  m <- get
  lift (foldrM (\n2 g ->
    if storeId n1 == n2 then return g
    else
      crossEdge n1 n2 tar e g) g (M.keys m))

crossEdge :: Node -> Node -> Node -> ImplGrEdge -> ImplGr -> StateT SolveState IO ImplGr
crossEdge n1 n2 tar e g = do
    liftIO $ putStrLn ("crossing " ++ show n1 ++ " " ++ show n2 ++ " " ++ show tar)
    addAndNode [n1, n2] tar e g

storeId :: Node -> Node
storeId n =
  let ([sId, sInst, _], _) = n
  in ([sId], sInst)


backEdges' :: ImplGr -> [((Node, Node), ImplGrEdge)]
backEdges' = G.backEdges . withoutModNodes

withoutModNodes :: ImplGr -> ImplGr
withoutModNodes =
  G.filterVerts
    (\v -> not (has _AndNode v || has _OrInputNode v || has _OrOutputNode v || has _FoldedNode v))

noFieldVars :: [Var] -> [Var]
noFieldVars = filter (not . has T._Array . T.typeOf)

gNoFieldVars :: ImplGr -> ImplGr
gNoFieldVars = G.mapVerts (\case
  InstanceNode (vs, f) -> InstanceNode (map noFieldVars vs, f)
  n -> n)

storeUnfold g = do
  g' <- storeElimination g >>= selectElimination
  lift (foldBackedges (backEdges' g') g')

shapeStep g = do
  g' <- lift (foldrM unfold g (backEdges' g))
  g'' <- storeUnfold g'
  let re = G.reached ([0], 0) g''
  let toEval = G.filterIdxs (`elem` G.idxs re) g''
  sol <- liftIO (interpolate toEval)
  case sol of
    Left m -> error (prettyShow m)
    Right interped -> do
      b <- liftIO $ isInductive ([0], 0) interped
      if b then
        return (Right interped)
      else do
        liftIO $ putStrLn "not inductive"
        liftIO $ G.display "step" interped
        return (Left g')

-- shape :: StateT ShapeState (StateT SolveState IO) ImplGr
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
  sol <- evalStateT (
        evalStateT (shape 2 g') M.empty
        ) (emptySolveState g')
  -- putStrLn (prettyShow $ entailmentChc (noBackedges sol))
  G.display "elim2" sol
