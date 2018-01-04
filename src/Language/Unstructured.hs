module Language.Unstructured where

import           Control.Lens
import           Control.Monad.State

import           Data.Pointed
import           Data.Data (Data)
import qualified Data.Set as S
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.List (nub)
import           Data.Text.Prettyprint.Doc
import           Data.Loc
import qualified Data.Optic.Directed.HyperGraph as G
import           Data.Optic.Directed.HyperGraph (Graph)

import           Logic.Formula
import           Logic.ImplicationGraph

import Debug.Trace

-- | An unstructured program contains no structured loops of if statements.
-- Instead it supports only jumps (conditional and unconditional) and procedure
-- calls as control flow elements.
data Com
  -- Set the variable to the value of the formula and proceed to the next instruction.
  = Var := Form
  -- Jump unconditionally to the specified instruction.
  | Jump Integer
  -- Jump to the specified instruction if the condition holds. Otherwise, proceed to
  -- the next instruction.
  | Cond Form Integer
  -- Call the named procedure with the given arguments, assigning the results to the
  -- given variables. Then, proceed to the next instruction.
  | Call ProcName [Form] [Var]
  -- A special marker indicating the end of the procedure. Every procedure should
  -- have a `Done` marker as the last instruction.
  | Skip
  | Done
  deriving (Show, Read, Eq, Ord, Data)

instance Pretty Com where
  pretty = \case
    v := f        -> pretty v <+> pretty ":=" <+> pretty f
    Jump i        -> pretty "jump" <+> pretty i
    Cond f i      -> pretty "cond" <+> pretty f <+> pretty i
    Call pn as rs -> pretty "call" <+> pretty pn <+> pretty as <+> pretty rs
    Skip          -> pretty "skip"
    Done          -> pretty "done"

type ProcName = String

type Imp = [(Com, [Var])]

-- | A program is a map of procedures, where the procedures are indexed by
-- their name. There is also a distinuished procedure name which is the entry
-- point of the program.
data Program =
  Program
  { _entryPoint :: ProcName
  , _procedures :: Map ProcName ([Var], [Var], Imp)
  } deriving (Show, Read, Eq, Ord, Data)

instance Pretty Program where
  pretty (Program ep ps) =
    pretty ep <+> pretty (M.toList ps)

-- | Transform a program and property into a graph.
impGraph :: Edge f => Program -> Graph Loc (f Form) Inst
impGraph (Program ep ps) =
  let (_, _, m, ord) = execState (organize ep) (-1, S.empty, M.empty, [])
      ps' = M.mapWithKey (renumber (fmap (\(c, _, _) -> c) m)) ps
      allIs = foldr (\pn -> (((ps' M.! pn) ^. _3) ++)) [] ord
  in instsToGraph m allIs
  where
    renumber m pn (args, params, is) =
      let offset = m M.! pn - toInteger (length is) + 1 in
      (args, params, map (\case
        (Jump i, vs) -> (pn, Jump (i + offset), nub $ args ++ vs)
        (Cond f i, vs) -> (pn, Cond f (i + offset), nub $ args ++ vs)
        (i, vs) -> (pn, i, nub $ args ++ vs)) is)

    organize pn = do
      s <- use _2
      when (pn `notElem` s) $
        case M.lookup pn ps of
          Nothing -> return ()
          Just (inputs, outputs, insts) -> do
            _2 %= S.insert pn
            mapM_ (\case
              (Call pn' _ _, _) -> organize pn'
              _ -> return ()) insts
            c <- use _1
            let endOfProc = c + toInteger (length insts)
            _1 .= endOfProc
            _3 %= M.insert pn (endOfProc, inputs, outputs)
            _4 %= (++ [pn])

instsToGraph :: Edge f
             => Map ProcName (Integer, [Var], [Var])
             -> [(ProcName, Com, [Var])] -> Graph Loc (f Form) Inst
instsToGraph callM cs = prune $ G.fromLists verts edges
-- instsToGraph callM cs = G.fromLists verts edges
  where
    endProg = toInteger $ length cs - 1
    procEnds = 0 : map ((+1) . view _1) (M.elems callM)
    verts = tail $
      zipWith vertOf [0..] (map (view _3) cs) ++ [(Loc endProg, Inst (Loc endProg) [] (LBool True))]
    edges = concat $ zipWith edgesOf [0..] cs

    vertOf l vs = (Loc l, emptyInst (Loc l) (map (setLoc l) vs))

    edgesOf l (pn, c, vs) = case c of
      v := f ->
        let f' = (f & vars %~ setLoc l)
            vs' = filter (/= v) vs
        in
        [ edgeFrom l (l+1)
          $ mkAnd
              (mkEql (typeOf v) (V $ setNew $ setLoc (l+1) v) f')
              (varCarry l (l+1) vs')
        ]
      Jump l' ->
        [ edgeFrom l l' $ varCarry l l' vs ]
      Skip ->
        [ edgeFrom l (l+1) $ varCarry l (l+1) vs ]
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
      Call pn' inputs outputs ->
        case M.lookup pn' callM of
          Nothing -> []
          Just (l', inps, outs) ->
            let prelocs =
                  if l `elem` procEnds
                  then [Loc l']
                  else [Loc l, Loc l'] in
            [ (G.HEdge (S.fromList prelocs) (Loc (l+1))
            , point $ manyAnd
                [ groupUp (inputs & vars %~ setLoc l)
                          (map V inps & vars %~ setLoc l')
                , groupUp (map V outputs & vars %~ setNew & vars %~ setLoc (l+1))
                          (map V outs & vars %~ setLoc l')
                , varCarry l (l+1) (filter (`notElem` outputs) vs)
                ])
            ]
      Done ->
        case M.lookup pn callM of
          Nothing -> []
          Just (l', _, _) ->
            if l == l' then [] else [ edgeFrom l l' $ varCarry l l' vs ]

    setLoc l v = v & varLoc .~ l
    setNew v = v & varNew .~ True
    edgeFrom l l' e =
      if l `elem` procEnds
      then (G.HEdge S.empty (Loc l'), point e)
      else (G.HEdge (S.singleton (Loc l)) (Loc l'), point e)

    varCarry l l' vs =
      let bef = vs & map (setLoc l)
          aft = vs & map (setLoc l') & map setNew
      in groupUp (map V bef) (map V aft)

    groupUp as bs = manyAnd $ zipWith (\a b -> mkEql (typeOf a) a b) as bs
