{-# LANGUAGE OverloadedStrings #-}
module Data.Ord.Graph.Extras where

import Control.Lens
import Data.Ord.Graph
import Data.Maybe (fromJust)
import Data.Monoid ((<>))
import qualified Turtle
import Text.PrettyPrint.HughesPJClass (Pretty, prettyShow)

backEdges :: Ord i => Graph i e v -> [((i, i), e)]
backEdges g = filter (\((i1, i2), _) -> i2 <= i1) $ g ^@.. iallEdges

display :: (Eq i, Pretty i, Pretty e, Pretty v)
        => FilePath -> Graph i e v -> IO ()
display fn g = do
  let txt = dot ": " prettyShow prettyShow prettyShow g
  writeFile fn txt
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
  in
    "digraph {\n" ++ unlines (map ("  " ++) (vs ++ es)) ++ "}"
  where
    lbls = zip (idxs g) [0..]
    lbl i = show $ fromJust $ lookup i lbls

    showVert (i, v) =
      lbl i ++ " [label=\"" ++ fi i ++ sep ++ fv v ++ "\"];"
    showEdge ((i1, i2), e) =
      lbl i1 ++ " -> " ++ lbl i2 ++ " [label=\"" ++ fe e ++ "\"];"
