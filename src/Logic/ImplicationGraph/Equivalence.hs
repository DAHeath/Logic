module Logic.ImplicationGraph.Equivalence where

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Except

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Optic.Graph (Graph)
import qualified Data.Optic.Graph as G
import qualified Data.Optic.Graph.Extras as G
import           Data.Text.Prettyprint.Doc
import           Data.These

import qualified Logic.Type as T
import           Logic.Formula
import           Logic.Var
import           Logic.Model
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Induction

type ProdGr i = ImplGr i (These Edge Edge)

instance (Pretty a, Pretty b) => Pretty (These a b) where
  pretty = \case
    This a -> pretty "This" <+> pretty a
    That b -> pretty "That" <+> pretty b
    These a b -> pretty "These" <+> pretty a <+> pretty "|" <+> pretty b

-- | Repeatedly unwind the program until a counterexample is found or inductive
-- invariants are found.
solve :: MonadIO m
      => Integer
      -> Integer
      -> Form
      -> Graph Integer Edge Vert
      -> Graph Integer Edge Vert
      -> m (Either Model (ProdGr Idx))
solve e1 e2 quer g1 g2 = do
  G.display "before" wQuery
  let wQuery' = fromGraph wQuery
  case wQuery' of
    Nothing -> error "bad input graph"
    Just gr -> loop equivStrat gr
  where
    wQuery =
      equivProduct g1 g2
      & G.addVert end (QueryV quer)
      & G.addEdge (end-1) end (This $ Edge (LBool True) M.empty)

    locMerge i j = j + i * (maxJ + 1)
    maxJ = maximum (G.idxs g2)
    end = locMerge e1 e2 + 1
    equate (v1, v2) = mkEql (T.typeOf v1) (V v1) (V v2)

    equivProduct g1 g2 =
      G.cartesianProductWith edgeMerge const locMerge vertMerge
        (G.mapEdges This g1) (G.mapEdges That g2)

    edgeMerge (This e1) (That e2) = These e1 e2
    edgeMerge e1 _ = e1

    vertMerge v1 v2 = case (v1, v2) of
      (InstanceV vs1 _, InstanceV vs2 _) -> emptyInst (vs1 ++ vs2)
      _ -> error "query in middle of equivalence graph"

equivStrat :: Strategy (These Edge Edge)
equivStrat =
  let theStrat = Strategy
        { backs = concatMap allEs . G.backEdges
        , interp = \g -> do
            sol <- interpolate (g & implGr %~ G.mapEdges edge)
            return $ fmap (\g' ->
              let vs = g' ^@.. implGr . G.iallVerts
              in foldr (\(i', v') g'' -> g'' & implGr %~ G.addVert i' v') g vs) sol
        , predInd = \g i -> do
            let (ls, rs) = preds g i
            lInd <- allInd (predInd theStrat) g i ls
            rInd <- allInd (predInd theStrat) g i rs
            return [lInd && not (null ls), rInd && not (null rs), null ls && null rs]
        }
  in theStrat
  where
    edge = \case
      This e -> e
      That e -> e
      These _ _ -> undefined
    allEs ((i1, i2), e) = case e of
      These e1 e2 -> [((i1, i2), This e1), ((i1, i2), That e2)]
      e' -> [((i1, i2), e')]
    preds g i = mconcat $ map (\(i', e) ->
      fromThese [] [] $ bimap (const [i']) (const [i']) e) $ g ^@.. implGr . G.iedgesTo i
