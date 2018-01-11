{-# LANGUAGE OverloadedStrings #-}
module Grammar.Plot where

import           Control.Lens
import           Control.Monad.State

import           Data.Monoid ((<>))
import           Data.List (intercalate)
import qualified Data.Set as S
import           Data.Text.Prettyprint.Doc hiding ((<>), dot)

import qualified Turtle
import           System.Info

import           Grammar.Grammar

plot :: MonadIO m => FilePath -> Grammar -> m ()
plot fn g = do
  let txt = dot g
      cmdopen = case System.Info.os of
        "mingw32" -> "start"
        "linux"   -> "xdg-open"
        _         -> "open"
  liftIO $ writeFile (fn ++ ".dot") txt
  let fn' = Turtle.fromString (fn ++ ".dot")
  _ <- Turtle.shell ("dot -Tpdf " <> fn' <> "> " <> fn' <> ".pdf") Turtle.empty
  _ <- Turtle.shell (cmdopen <> " " <> fn' <> ".pdf") Turtle.empty
  return ()

dot :: Grammar -> String
dot g =
  let vs = map symbol (S.toList (symbols g))
      es = concatMap rule (g ^. grammarRules)
      globalAtts = [ "node[fontsize=6];"
                   , "edge[fontsize=6, arrowsize=0.6];"]
  in "digraph {\n" ++ unlines (map ("  " ++) (globalAtts ++ vs ++ es)) ++ "}"
  where
    symbol i = show i ++ ";"
    rule (Rule ct lhs f rhs) =
      let annot = " [label=\"" ++ show ct ++ ": " ++ show (pretty f) ++ "\"];"
          inc = rhs ^.. allSymbols
          tar = lhs ^. productionSymbol
      in case inc of
        [i] -> [show i ++ " -> " ++ show tar ++ annot]
        _ ->
          let mid = "m" ++ intercalate "_" (map show (inc ++ [tar])) in
          [ mid ++ " [shape=point, width=0.00001, height=0.00001];" ]
          ++ map (\i -> show i ++ " -> " ++ mid ++ " [dir=none];") inc
          ++ [ mid ++ " -> " ++ show tar ++ annot ]
