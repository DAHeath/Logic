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

import           System.Info

display :: (MonadIO m, Eq i, Pretty i, Pretty e, Pretty v)
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

dot :: Eq i
    => String -> (i -> String) -> (e -> String) -> (v -> String)
    -> Graph i e v -> String
dot seper fi fe fv g =
  let vs = map showVert (g ^@.. iallVerts)
      es = map showEdge (g ^@.. iallEdges)
      globalAtts = ["node[fontsize=6];", "edge[fontsize=6];"]
  in

    "digraph {\n" ++ unlines (map ("  " ++) (globalAtts ++ vs ++ es)) ++ "}"
  where
    lbls = zip (idxs g) ([0..] :: [Integer])
    lbl i = show $ fromJust $ lookup i lbls

    showVert (i, v) =
      lbl i ++ " [label=\"" ++ fi i ++ seper ++ fv v ++ "\"];"
    showEdge ((i1, i2), e) =
      lbl i1 ++ " -> " ++ lbl i2 ++ " [label=\"" ++ fe e ++ "\"];"
