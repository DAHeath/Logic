{-# LANGUAGE OverloadedStrings #-}

module Logic.ImplicationGraph.JavaParser where

import           Data.Optic.Graph (Graph)
import           Logic.ImplicationGraph (Edge, Vert)
import           Logic.ImplicationGraph.JSONParser (parseGraphFromJSON, Line)

import           Text.Printf (printf)
import           Data.Text.Encoding (encodeUtf8)
import           Data.ByteString.Lazy (fromStrict)
import           System.IO (FilePath)
import           Control.Foldl as Foldl
import           Control.Monad.Trans.Maybe

import qualified Turtle


java2graph :: FilePath -> String -> MaybeT IO (Graph Line Edge Vert)
java2graph file method = do
  json <- MaybeT $ Turtle.fold sh Foldl.head -- first line is the JSON data
  MaybeT $ return $ parse json
  where
    parse = parseGraphFromJSON . fromStrict . encodeUtf8 . Turtle.lineToText
    cmd = printf "java2graph print-implication -c '%s' -m '%s'" file method
    sh = Turtle.inshell (Turtle.fromString cmd) Turtle.empty
