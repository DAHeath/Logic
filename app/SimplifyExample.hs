{-# LANGUAGE QuasiQuotes #-}
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Directed.HyperGraph as G
import qualified Data.Optic.Graph.Extras as G
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Text.Prettyprint.Doc
import qualified Data.ByteString.Lazy.Char8 as BS
import           Data.Maybe (fromJust)

import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Safety
import           Logic.ImplicationGraph.Simplify as S
import           Logic.ImplicationGraph.JSONParser (parseGraphFromJSON)
import           Logic.ImplicationGraph.LTree
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
        let pruned = S.prune (G.mapEdge Leaf $ fromGraph parsedGraph)
        putStrLn "Trying to simplify JSON..."
        G.display "before.dot" parsedGraph
        G.display "simplified.dot" pruned

        sol <- solve parsedGraph
        case sol of
          Left m -> do
            putStrLn "Could not prove safety:"
            print (pretty m)
          Right r -> do
            putStrLn "Safe!"
            G.display "solved.dot" r

i :: Var Counted
i  = Free (Counted ["i"] 0) T.Int

bump :: Var Counted -> Integer -> Var Counted
bump (Free (Counted p c) t) b = Free (Counted p (c + b)) t
bump o _ = o

emptyEdge :: (Ord i) => i -> i -> (G.HEdge i, Edge Counted)
emptyEdge s d = (G.HEdge (S.singleton s) d, Edge [form|i:Int = 0|] M.empty)

irreducibleExample :: Graph Loc (Edge Counted) (Inst Counted)
irreducibleExample = G.fromLists
    [ (Loc 0, emptyInst (Loc 0) [])
    , (Loc 1, emptyInst (Loc 1) [])
    , (Loc 2, emptyInst (Loc 2) [])
    , (Loc 3, emptyInst (Loc 3) [])
    , (Loc 4, emptyInst (Loc 4) [])
    , (Loc 5, emptyInst (Loc 5) [])]
    [ emptyEdge (Loc 0) (Loc 1)
    , emptyEdge (Loc 1) (Loc 2)
    , emptyEdge (Loc 2) (Loc 4)
    , emptyEdge (Loc 4) (Loc 5)
    , emptyEdge (Loc 1) (Loc 3)
    , emptyEdge (Loc 3) (Loc 4)
    , emptyEdge (Loc 3) (Loc 5)
    , emptyEdge (Loc 4) (Loc 1)]

disjunctionExample :: (Edge Counted, Edge Counted)
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
