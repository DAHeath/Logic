{-# LANGUAGE QuasiQuotes #-}
import           Control.Lens

import           Data.Optic.Graph (Graph)
import qualified Data.Optic.Graph as G
import qualified Data.Optic.Graph.Extras as G
import qualified Data.Map as M
import           Data.Text.Prettyprint.Doc
import qualified Data.ByteString.Lazy.Char8 as BS
import           Data.Maybe (fromJust)

import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Safety
import           Logic.ImplicationGraph.Simplify as S
import           Logic.ImplicationGraph.JSONParser (parseGraphFromJSON)
import qualified Logic.Type as T
import           Logic.Formula
import           Logic.Formula.Parser
import           Logic.Var

main :: IO ()
main = let
        ir = S.irreducible irreducibleExample
        dj = uncurry S.disjunction disjunctionExample
    in do
        print "Irreducible example:"
        print ir

        print "Disjunction example:"
        print $ _edgeMap dj
        print $ pretty $ _edgeForm dj

        parsedGraph <- fromJust . parseGraphFromJSON <$> BS.readFile "test.json"
        let pruned = parsedGraph & implGr %~ S.prune
        putStrLn "Trying to simplify JSON..."
        G.display "before.dot" (parsedGraph ^. implGr)
        G.display "simplified.dot" (pruned ^. implGr)

        sol <- solve pruned
        case sol of
          Left m -> do
            putStrLn "Could not prove safety:"
            print (pretty m)
          Right r -> do
            putStrLn "Safe!"
            G.display "solved.dot" (r ^. implGr)
            print . pretty . M.toList =<< collectAnswer r

i :: Var
i  = Free ["i"] 0 T.Int

bump :: Var -> Int -> Var
bump (Free p c t) b = Free p (c + b) t
bump o _ = o

emptyEdge :: (Ord i) => i -> i -> (i, i, Edge)
emptyEdge s d = (s, d, Edge [form|i:Int = 0|] M.empty)

irreducibleExample :: Graph Int Edge Vert
irreducibleExample = G.fromLists
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

disjunctionExample :: (Edge, Edge)
disjunctionExample =
    let
        i' = bump i 1
        i'' = bump i 2

        e1 = Edge {
            _edgeMap = M.fromList [(i, i')],
            _edgeForm = foldl1 mkAnd
                        [ Eql T.Int :@ V i :@ LInt 0
                        , Eql T.Int :@ V i' :@ V i]
        }

        e2 = Edge {
            _edgeMap = M.fromList [(i, i'')],
            _edgeForm = foldl1 mkAnd
                        [Eql T.Int :@ V i :@ LInt 0
                        , Eql T.Int :@ V i' :@ V i
                        , Eql T.Int :@ V i'' :@ V i']
        }
    in
        (e1, e2)
