module Logic.ImplicationGraph.Equivalence where

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Except

import           Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G
import qualified Data.Optic.Graph.Extras as G
import           Data.Text.Prettyprint.Doc
import           Data.These

import qualified Logic.Type as T
import           Logic.Formula
import           Logic.Var
import           Logic.Model
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Induction
import           Logic.ImplicationGraph.Chc

type ProdGr = ImplGr (These Edge Edge)

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
      -> m (Either Model ProdGr)
solve e1 e2 quer g1 g2 = do
  G.display "before" wQuery
  let gr = fromGraph wQuery
  loop equivStrat gr
  where
    wQuery =
      equivProduct g1 g2
      & G.addVert end (Vert (locMerge e1 e2 + 1) [] quer)
      & G.addEdge (G.HEdge (S.singleton $ end-1) end) (This $ Edge (LBool True) M.empty)

    locMerge i j = j + i * (maxJ + 1)
    maxJ = maximum (G.idxs g2)
    end = locMerge e1 e2 + 1
    equate (v1, v2) = mkEql (T.typeOf v1) (V v1) (V v2)

    equivProduct g1 g2 =
      cleanIntros (G.cartesianProductWith edgeMerge const locMerge vertMerge
                    (G.mapEdge This g1) (G.mapEdge That g2))

    cleanIntros g =
      let es = g ^@.. G.iallEdges
      in G.delIdx 0 $ foldr (\(G.HEdge i1 i2, e) g ->
        G.addEdge (G.HEdge (S.filter (/= 0) i1) i2) e (G.delEdge (G.HEdge i1 i2) g)) g es

    edgeMerge (This e1) (That e2) = These e1 e2
    edgeMerge e1 _ = e1

    vertMerge v1 v2 = case (v1, v2) of
      (Vert i vs1 _, Vert j vs2 _) -> emptyInst (locMerge i j) (vs1 ++ vs2)

equivStrat :: Strategy (These Edge Edge)
equivStrat =
  let theStrat = Strategy
        { backs = concatMap allEs . G.backEdges
        , interp = \g -> do
            sol <- interpolate (G.mapEdge edge g)
            return $ fmap (\g' ->
              let vs = g' ^@.. G.iallVerts
              in foldr (\(i', v') g'' -> G.addVert i' v' g'') g vs) sol
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
    allEs (i, e) = case e of
      These e1 e2 -> [(i, This e1), (i, That e2)]
      e' -> [(i, e')]
    preds g i = mconcat $ map (\(G.HEdge i' _, e) ->
      fromThese [] [] $ bimap (const (S.toList i')) (const (S.toList i')) e)
      $ g ^@.. G.iedgesTo i
