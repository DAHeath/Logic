{-# LANGUAGE QuasiQuotes #-}
module Language.Unstructured where

import           Control.Lens
import           Control.Arrow (second)
import           Control.Monad.State

import           Data.Data (Data)
import qualified Data.Set as S
import           Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Optic.Directed.HyperGraph as G
import           Data.Optic.Directed.HyperGraph (Graph)
import qualified Data.Optic.Graph.Extras as G
import           Data.Text.Prettyprint.Doc

import           Logic.Formula.Parser
import qualified Logic.Type as T
import           Logic.Formula
import           Logic.Var
import           Logic.ImplicationGraph
import           Logic.ImplicationGraph.Simplify
import           Logic.ImplicationGraph.LTree
import           Logic.ImplicationGraph.Safety

data Com
  = Var := Form
  | Jump Integer
  | Cond Form Integer
  | Call ProcName [Form] [Var]
  | Done
  deriving (Show, Read, Eq, Ord, Data)

instance Pretty Com where
  pretty = \case
    v := f        -> pretty v <+> pretty ":=" <+> pretty f
    Jump i        -> pretty "JUMP" <+> pretty i
    Cond f i      -> pretty "COND" <+> pretty f <+> pretty i
    Call pn as rs -> pretty "CALL" <+> pretty pn <+> pretty as <+> pretty rs
    Done          -> pretty "DONE"

type ProcName = String

type Imp = [(Com, [Var])]

data Program =
  Program
  { _entryPoint :: ProcName
  , _procedures :: Map ProcName ([Var], [Var], Imp)
  } deriving (Show, Read, Eq, Ord, Data)

instance Pretty Program where
  pretty (Program ep ps) =
    pretty ep <+> pretty (M.toList ps)

-- | Transform a program and property into a graph.
impGraph :: Form -> Program -> Graph Loc Edge Inst
impGraph f (Program ep ps) =
  let (_, _, m) = execState (organize ep) (0, S.empty, M.empty)
      ps' = M.mapWithKey (renumber (fmap (\(c, _, _) -> c) m)) ps
  in
  instsToGraph m f (concatMap (\(_, _, is) -> is) (M.elems ps))
  where
    renumber m pn (ret, params, is) =
      let offset = m M.! pn - toInteger (length is) in
      (params, map (\case
        (Jump i, vs) -> (Jump (i + offset), vs)
        (Cond f i, vs) -> (Cond f (i + offset), vs)
        c -> c) is)

    organize pn = do
      (c, s, m) <- get
      if pn `elem` s then return ()
      else case M.lookup pn ps of
        Nothing -> return ()
        Just (inputs, outputs, insts) -> do
          let end = c + toInteger (length insts) - 1
          put (end, S.insert pn s, M.insert pn (end, inputs, outputs) m)
          mapM_ (\case
            (Call pn' _ _, []) -> organize pn'
            _ -> return ()) insts

instsToGraph :: Map ProcName (Integer, [Var], [Var]) -> Form -> Imp -> Graph Loc Edge Inst
instsToGraph callM q cs =
  let g = G.fromLists verts edges
      vs' = map (setLoc (end+1)) (g ^?! ix (Loc end) . instVars)
  in
  g & G.addVert (Loc (end+1)) (Inst (Loc (end+1))
                                    vs'
                                    (q & vars %~ setLoc (end + 1)))
    & G.addEdge (G.HEdge (S.singleton (Loc end)) (Loc (end+1))) (Leaf $ varCarry end (end+1) vs')
  where
    end = toInteger $ length cs - 1
    verts = tail $
      zipWith vertOf [0..] (map snd cs) ++ [(Loc end, Inst (Loc end) [] (LBool True))]
    edges = map (second Leaf) $ concat $ zipWith edgesOf [0..] cs

    vertOf l vs = (Loc l, emptyInst (Loc l) (map (setLoc l) vs))

    edgesOf l (c, vs) = case c of
      v := f ->
        let f' = (f & vars %~ setLoc l)
            vs' = filter (/= v) vs
        in
        [ edgeFrom l (l+1)
          $ mkAnd
              (mkEql (T.typeOf v) (V $ setNew $ setLoc (l+1) v) f')
              (varCarry l (l+1) vs')
        ]
      Jump l' ->
        [ edgeFrom l l' $ varCarry l l' vs ]
      Cond f l' ->
        [ edgeFrom l l'
          $ mkAnd
              (f & vars %~ setLoc l)
              (varCarry l l' vs)
        , edgeFrom l (l+1)
          $ mkAnd
              (mkNot f & vars %~ setLoc l)
              (varCarry l (l+1) vs)
        ]
      Call pn inputs outputs ->
        case M.lookup pn callM of
          Nothing -> []
          Just (l', inps, outs) ->
            let list = case l of
                        0 -> [Loc l']
                        n -> [Loc n, Loc l'] in
            [ (G.HEdge (S.fromList list) (Loc (l+1))
            , manyAnd
                [ groupUp (inputs & vars %~ setLoc l)
                          (map V inps & vars %~ setLoc l')
                , groupUp (map V outputs & vars %~ setNew & vars %~ setLoc (l+1))
                          (map V outs & vars %~ setLoc l')
                , varCarry l (l+1) (filter (`notElem` outs) vs)
                ])
            ]
      Done -> []

    setLoc l v = v & _Free . _1 . freeVLoc .~ l
    setNew v = v & _Free . _1 . freeVNew .~ True
    edgeFrom l l' e =
      if l == 0
      then (G.HEdge S.empty (Loc l'), e)
      else (G.HEdge (S.singleton (Loc l)) (Loc l'), e)

    varCarry l l' vs =
      let bef = vs & map (setLoc l)
          aft = vs & map (setLoc l') & map setNew
      in groupUp (map V bef) (map V aft)

    groupUp as bs = manyAnd $ zipWith (\a b -> mkEql (T.typeOf a) a b) as bs

x = Free (FreeV ["x"] 0 False) T.Int
n = Free (FreeV ["n"] 0 False) T.Int
r = Free (FreeV ["r"] 0 False) T.Int

proc :: Imp
proc =
  [ (x := [form|0|], [])                         -- 0
  , (Cond [form|not (x:Int < n:Int)|] 4, [x, n]) -- 1
  , (x := [form|x:Int + 2|], [x, n])             -- 2
  , (Jump 1, [x, n])                             -- 3
  , (Done, [x,n])                                -- 4
  ]

-- test = impGraph [form|not (x:Int = 7)|] prog


program :: Program
program = Program
  { _entryPoint = "f"
  , _procedures =
    M.singleton "f" ([n, x], [r],
      [ (Cond [form|not (n:Int <= 0)|] 3, [r,n,x])
      , (r := [form|x:Int|], [r,n,x])
      , (Jump 4, [r,n,x])
      , (Call "f" [[form|n:Int - 1|], [form|x:Int + n:Int|]] [r], [r,n,x])
      , (Done, [r,n,x])
      ])
  }
