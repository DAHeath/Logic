module Logic.ImplicationGraph.Optimize (
    irreducible
) where

import qualified Data.Optic.Graph as G
import qualified Data.Optic.Graph.Extras as G

import           Logic.ImplicationGraph

-- | Finds irreducible vertices in a given `Graph`.
irreducible, irreducible' :: (Ord i) => ImplGr i -> [i]
irreducible graph =
    case indices of
        []  -> []
        _   -> irreducible' graph
    where
        indices = G.idxs graph

irreducible' graph = [startIndex, queryIndex] ++ loopHeaders where
    indices = G.idxs graph
    startIndex = minimum indices
    queryIndex = maximum indices

    -- The loop headers correspond to the destination vertices of back edges.
    loopHeaders = map (\((_, s), _) -> s) $ G.backEdges graph
 