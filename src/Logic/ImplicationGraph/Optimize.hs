module Logic.ImplicationGraph.Optimize (
    irreducible
) where

import           Control.Lens

import           Data.List (length, intersect)
import qualified Data.Optic.Graph as G
import qualified Data.Optic.Graph.Extras as G

import           Logic.ImplicationGraph

-- | Finds the exit nodes of a loop.
exitNodes :: ImplGr LinIdx -> [LinIdx] -> [LinIdx]
exitNodes graph loop = filter exitNode loop where
    -- Any edge coming _out_ of a loop subgraph is an exit node.
    -- Check whether or not any edge coming out of `idx` has a destination
    -- outside of the loop.
    exitNode idx = any (\(i, _) -> not $ i `elem` loop) (edges idx)
    -- Edges originating in `idx`.
    edges idx = graph ^@.. G.iedgesFrom idx

-- | Finds irreducible vertices in a given `Graph`.
irreducible :: ImplGr LinIdx -> [LinIdx]
irreducible graph =
    case indices of
        []  -> []
        _   -> irreducible' graph
    where
        indices = G.idxs graph

irreducible' :: ImplGr LinIdx -> [LinIdx]
irreducible' graph = [startIndex, queryIndex] ++ loopHeaders ++ loopExits where
    indices = G.idxs graph
    startIndex = minimum indices
    queryIndex = maximum indices

    backEdges = G.backEdges graph
    sccs = G.scc graph

    -- The loop headers correspond to the destination vertices of back edges.
    loopHeaders = map (\((s, _), _) -> s) backEdges
    -- Loops (header, body and exit vertices) correspond to strongly connected
    -- components that include loop headers.
    loops = filter (\scc -> (length $ scc `intersect` loopHeaders) > 0) sccs
    loopExits = concat $ map (exitNodes graph) loops
 