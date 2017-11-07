{-# LANGUAGE QuasiQuotes #-}

import           Data.Optic.Graph (Graph)
import qualified Data.Optic.Graph as G
import qualified Data.Optic.Graph.Extras as G
import qualified Data.Map as M

import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Optimize (irreducible)
import qualified Logic.Type as T
import           Logic.Formula.Parser
import           Logic.Var

main :: IO ()
main = do
    print $ irreducible example

i :: Var
i  = Free "i" T.Int

emptyEdge :: (Ord i) => i -> i -> (i, i, Edge)
emptyEdge s d = (s, d, Edge [form|i:Int = 0|] M.empty)

example :: Graph Int Edge Vert
example = G.fromLists
    [ (0, emptyInst [])
    , (1, emptyInst [])
    , (2, emptyInst [])
    , (3, emptyInst [])
    , (4, emptyInst [])
    , (5, emptyInst [])]
    [ emptyEdge 0 1
    , emptyEdge 1 2
    , emptyEdge 2 4
    , emptyEdge 4 5
    , emptyEdge 1 3
    , emptyEdge 3 4
    , emptyEdge 3 5
    , emptyEdge 4 1]
