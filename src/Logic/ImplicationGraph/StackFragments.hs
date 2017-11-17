module Logic.ImplicationGraph.StackFragments where

import           Control.Lens

import           Data.Maybe (fromJust)
import           Data.Optic.Graph (Graph)
import qualified Data.Optic.Graph as G
import qualified Data.Optic.Graph.Extras as G


import           Logic.ImplicationGraph
import           Logic.Formula as F

import qualified Data.Map as M

-- | Calculate the implication graph that also has stack fragments.
--
-- For each hyperedge add a new non-hyperedge from the pair of locations
fragmented :: MonadState SolveState m => ImplGr e -> m (ImplGr e)
fragmented = undefined



g :: ImplGr Edge
g = fromJust $ fromGraph (
  G.fromLists
    [ (0 :: Integer, emptyInst [])
    , (1, emptyInst [])
    , (2, QueryV (LBool True))
    ]
    [ (0, 2, Edge (LBool True) M.empty)
    , (1, 2, Edge (LBool True) M.empty)
    ]) (M.singleton 2 [(0, 1)])

test :: IO ()
test = do
  G.display "test" (g ^. implGr)
