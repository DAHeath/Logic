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

emptyEdge s e = (LinIdx s 0, LinIdx e 0, Edge [form|i:Int = 0|] M.empty)

example :: Graph LinIdx Edge Vert
example = G.fromLists
    [ (LinIdx 0 0, emptyInst [])
    , (LinIdx 1 0, emptyInst [])
    , (LinIdx 2 0, emptyInst [])
    , (LinIdx 3 0, emptyInst [])
    , (LinIdx 4 0, emptyInst [])
    , (LinIdx 5 0, emptyInst [])]
    [ emptyEdge 0 1
    , emptyEdge 1 2
    , emptyEdge 1 4
    , emptyEdge 2 3
    , emptyEdge 3 1
    , emptyEdge 3 5
    , emptyEdge 4 3
    , emptyEdge 4 5]
