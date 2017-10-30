{-# LANGUAGE OverloadedStrings #-}
module Data.Optic.Graph.Extras where

import           Control.Lens
import           Control.Applicative.Backwards
import           Control.Monad.State

import           Data.Optic.Graph
import           Data.Maybe (fromJust)
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Monoid ((<>))
import           Data.Text.Prettyprint.Doc hiding ((<>), dot)

import           Prelude hiding (reverse)

import qualified Turtle

backEdges :: Ord i => Graph i e v -> [((i, i), e)]
backEdges g = filter (\((i1, i2), _) -> i2 <= i1) $ g ^@.. iallEdges

noBackEdges :: Ord i => Graph i e v -> Graph i e v
noBackEdges g =
  ifilterEdges (\i1 i2 _ -> (i1, i2) `notElem` map fst (backEdges g)) g

between :: Ord i => i -> i -> Graph i e v -> Graph i e v
between i1 i2 g =
  let is1 = idxSet (reached i1 g)
      is2 = idxSet (reaches i2 g)
      is = S.intersection is1 is2
  in filterIdxs (`elem` is) g

unwind :: (Applicative f, Ord i, Show i)
       => (i -> f i)
       -> (i -> i -> e -> f e)
       -> (i -> v -> f v)
       -> i -> i -> e
       -> Graph i e v -> f (i, Graph i e v)
unwind fi fe fv i1 i2 e g =
  let g' = reaches i2 (delEdge i1 i2 g) `mappend` between i2 i1 g
      am = M.fromList <$> traverse (\i -> fmap (\i' -> (i, i')) (Backwards $ fi i)) (idxs g')
      ae = fe i1 i2 e
      ag = idfs fe fv g'
  in complete i1 i2 <$> forwards am <*> ae <*> pure g <*> ag

  where
    complete i1 i2 m e g g' = ( M.findWithDefault i2 i2 m, connect m e g (unwind' m g'))
    unwind' m = mapIdxs (\i -> M.findWithDefault i i m)
    connect m e g g' = addEdge (M.findWithDefault i1 i1 m) i2 e $ union g g'

display :: (MonadIO m, Eq i, Pretty i, Pretty e, Pretty v)
        => FilePath -> Graph i e v -> m ()
display fn g = do
  let txt = dot ": " (show . pretty) (show . pretty) (show . pretty) g
  liftIO $ writeFile fn txt
  let fn' = Turtle.fromString fn
  _ <- Turtle.shell ("dot -Tpdf " <> fn' <> "> " <> fn' <> ".pdf") Turtle.empty
  _ <- Turtle.shell ("open " <> fn' <> ".pdf") Turtle.empty
  return ()

dot :: Eq i
    => String -> (i -> String) -> (e -> String) -> (v -> String)
    -> Graph i e v -> String
dot sep fi fe fv g =
  let vs = map showVert (g ^@.. iallVerts)
      es = map showEdge (g ^@.. iallEdges)
      globalAtts = ["node[fontsize=6];", "edge[fontsize=6];"]
  in

    "digraph {\n" ++ unlines (map ("  " ++) (globalAtts ++ vs ++ es)) ++ "}"
  where
    lbls = zip (idxs g) [0..]
    lbl i = show $ fromJust $ lookup i lbls

    showVert (i, v) =
      lbl i ++ " [label=\"" ++ fi i ++ sep ++ fv v ++ "\"];"
    showEdge ((i1, i2), e) =
      lbl i1 ++ " -> " ++ lbl i2 ++ " [label=\"" ++ fe e ++ "\"];"

cartesianProduct :: (Ord i1, Ord i2, Ord i3)
                 => (i1 -> i2 -> i3)
                 -> (v1 -> v2 -> v3)
                 -> Graph i1 e v1 -> Graph i2 e v2 -> Graph i3 e v3
cartesianProduct fi fv g1 g2 =
 if order g2 == 0 then empty else
 let vs1 = g1 ^@.. iallVerts
     vs2 = g2 ^@.. iallVerts
     vs = do
       (i1, v1) <- vs1
       (i2, v2) <- vs2
       return (fi i1 i2, fv v1 v2)
     es1 = g1 ^@.. iallEdges
     es2 = g2 ^@.. iallEdges
     es1' = do
       (i2, _) <- vs2
       ((i1, i1'), e) <- es1
       return (fi i1 i2, fi i1' i2, e)
     es2' = do
       (i1, _) <- vs1
       ((i2, i2'), e) <- es2
       return (fi i1 i2, fi i1 i2', e)
     in fromLists vs (es1' ++ es2')
