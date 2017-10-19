{-# LANGUAGE LambdaCase, TypeFamilies, FlexibleContexts, DeriveDataTypeable, ConstraintKinds #-}
module Logic.ImplicationGraph.Equivalence where

import           Control.Arrow (second)
import           Control.Lens
import           Control.Monad.State

import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.List.Split (splitOn)
import qualified Data.Ord.Graph as G

import           Logic.Formula
import           Logic.Model
import           Logic.ImplicationGraph.Solve
import           Logic.ImplicationGraph.Type
import           Logic.ImplicationGraph.Interpolate
import           Logic.ImplicationGraph.Induction

import           Text.PrettyPrint.HughesPJClass (prettyShow, Pretty, pPrint, (<+>))

equivalence :: MonadIO m => ImplGr -> ImplGr -> m (Either Model (Map (Lbl, Lbl) Form))
equivalence = undefined

data PLbl = PLbl Lbl InstanceId Lbl InstanceId
  deriving (Show, Read, Eq, Ord, Data)

instance LblLike PLbl where
  type Base PLbl = (Int, Int)
  toBase (PLbl i1 _ i2 _) = (i1, i2)
  match x y = toBase x == toBase y
  toPrefix (PLbl i1 ins1 i2 ins2) = show i1 ++ "_" ++ show ins1 ++ "_" ++ show i2 ++ "_" ++ show ins2

  fromPrefix s =
    case splitOn "_" s of
      [i1, inst1, i2, inst2, rest] -> [(PLbl (read i1) (read inst1) (read i2) (read inst2), "_" ++ rest)]
      _ -> []

instance Pretty PLbl where
  pPrint (PLbl a b c d) = pPrint a <+> pPrint b <+> pPrint c <+> pPrint d

type PGr = ImplGr' PLbl
type PNode = Node' PLbl
type PSolve m = Solve PLbl m

orWiseProduct :: PSolve m => ImplGr -> ImplGr -> m PGr
orWiseProduct g1 g2 = do
    let vs = [(mergeN ix1 ix2, mergeV v1 v2) | (ix1, v1) <- g1 ^@.. G.iallVerts
                                             , (ix2, v2) <- g2 ^@.. G.iallVerts]
    let ixs = mergeN <$> G.idxs g1 <*> G.idxs g2

    (orIn, orM) <- runStateT (mapM orNode ixs) M.empty
    (orOut1, es1) <- edges True  orM g1 g2
    (orOut2, es2) <- edges False orM g2 g1
    let orEdges = map (\(n1, n2) -> (n1, n2, ImplGrEdge (LBool True) M.empty)) $ M.toList orM
    let lOrIn = map (\o -> (o, OrInputNode)) orIn
    let lOrOut = map (\o -> (o, OrOutputNode)) (orOut1 ++ orOut2)

    return $ G.fromLists (lOrIn ++ lOrOut ++ vs) (es1 ++ es2 ++ orEdges)
  where
    -- edges :: ImplGr -> ImplGr -> ([PNode], [((PNode, PNode), ImplGrEdge)])
    edges cond orM g1 g2 =
      let esToBuild = do
            n1 <- G.idxs g1
            n2 <- G.idxs g2
            (n1', e) <- g1 ^@.. G.iedgesFrom n1
            let start = M.findWithDefault undefined (condMerge cond n1 n2) orM
            let end = condMerge cond n1' n2
            return (start, end, e)
      in unzip <$> forM esToBuild (\(start, end, e) -> do
           oo <- newOrOutputNode
           let es = [(start, oo, ImplGrEdge (LBool True) M.empty), (oo, end, e)]
           return (oo, es))

    condMerge :: Bool -> Node -> Node -> PNode
    condMerge b n1 n2 = if b then mergeN n1 n2 else mergeN n2 n1

    mergeN :: Node -> Node -> PNode
    mergeN (iden1, inst1) (iden2, inst2) = (PLbl iden1 inst1 iden2 inst2, 0)

    mergeV :: ImplGrNode -> ImplGrNode -> ImplGrNode' PLbl
    mergeV n1 n2 = case (n1, n2) of
      (InstanceNode i1, InstanceNode i2) -> InstanceNode (mergeI i1 i2)

    mergeI :: Instance -> Instance -> Instance
    mergeI (vs1, f1) (vs2, f2) = ([head vs1, head vs2], mkAnd f1 f2)

    orNode :: PSolve m => PNode -> StateT (Map PNode PNode) m PNode
    orNode n = do
      o <- lift newOrInputNode
      modify (M.insert n o)
      return o

-- type Equi

-- equivStep
