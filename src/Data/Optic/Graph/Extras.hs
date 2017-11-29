{-# LANGUAGE OverloadedStrings #-}
module Data.Optic.Graph.Extras where

import           Control.Lens
import           Control.Applicative.Backwards
import           Control.Monad.State

import           Data.Optic.Directed.HyperGraph
import           Data.Maybe (fromJust)
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Monoid ((<>))
import           Data.Text.Prettyprint.Doc hiding ((<>), dot)

import           Prelude hiding (reverse)

import qualified Turtle

import           System.Info

display :: (MonadIO m, Ord i, Pretty i, Pretty e, Pretty v)
        => FilePath -> Graph i e v -> m ()
display fn g = do
  let txt = dot ": " (show . pretty) (show . pretty) (show . pretty) g
      cmdopen = case System.Info.os of
        "mingw32" -> "start"
        "linux"   -> "xdg-open"
        _         -> "open"
  liftIO $ writeFile fn txt
  let fn' = Turtle.fromString fn
  _ <- Turtle.shell ("dot -Tpdf " <> fn' <> "> " <> fn' <> ".pdf") Turtle.empty
  _ <- Turtle.shell (cmdopen <> " " <> fn' <> ".pdf") Turtle.empty
  return ()

dot :: Ord i
    => String -> (i -> String) -> (e -> String) -> (v -> String)
    -> Graph i e v -> String
dot seper fi fe fv g =
  let vs = map showVert (g ^@.. iallVerts)
      es = concatMap showEdge (g ^@.. iallEdges)
      globalAtts = [ "node[fontsize=6];"
                   , "edge[fontsize=6, arrowsize=0.6];"]
  in

    "digraph {\n" ++ unlines (map ("  " ++) (globalAtts ++ vs ++ es)) ++ "}"
  where
    lbls = zip (idxs g) ([0..] :: [Integer])
    lbl i = show $ fromJust $ lookup i lbls

    showVert (i, v) =
      lbl i ++ " [label=\"" ++ fi i ++ seper ++ fv v ++ "\"];"
    showEdge (HEdge i1 i2, e) =
      let back = if any (>= i2) i1 then ", style=dashed" else ""
          annot = " [label=\"" ++ fe e ++ "\"" ++ back ++"];"
      in

      case length i1 of
        1 -> map (\i -> lbl i ++ " -> " ++ lbl i2 ++ annot) (S.toList i1)
        n ->
          let mid = "m" ++ concatMap lbl (S.toList i1) ++ "_" ++ lbl i2
          in
          [ mid ++ " [shape=point, width=0.00001,height=0.00001" ++ back ++ "];" ]
          ++ map (\i -> lbl i ++ " -> " ++ mid ++ " [dir=none];") (S.toList i1)
          ++ [ mid ++ " -> " ++ lbl i2 ++ annot ]
