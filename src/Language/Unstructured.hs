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
import           Data.Text.Prettyprint.Doc

import qualified Logic.Type as T
import           Logic.Formula hiding (Store)
import           Logic.Var
import           Logic.ImplicationGraph

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
  | Done

  | Store Var Var Form Form
  | Load Var Var Form
  deriving (Show, Read, Eq, Ord, Data)

instance Pretty Com where
  pretty = \case
    v := f        -> pretty v <+> pretty ":=" <+> pretty f
    Jump i        -> pretty "JUMP" <+> pretty i
    Cond f i      -> pretty "COND" <+> pretty f <+> pretty i
    Call pn as rs -> pretty "CALL" <+> pretty pn <+> pretty as <+> pretty rs
    Done          -> pretty "DONE"

    Store objref valref obj val ->
      pretty "STORE" <+> pretty objref <+> pretty valref <+> pretty obj <+> pretty val
    Load  ref val obj -> pretty "LOAD"  <+> pretty ref <+> pretty val <+> pretty obj

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
impGraph :: Program -> Graph Loc Edge Inst
impGraph (Program ep ps) =
  let (_, _, m) = execState (organize ep) (0, S.empty, M.empty)
      ps' = M.mapWithKey (renumber (fmap (\(c, _, _) -> c) m)) ps
  in
  instsToGraph m (concatMap (\(_, _, is) -> is) (M.elems ps'))
  where
    renumber m pn (args, params, is) =
      let offset = m M.! pn - toInteger (length is) + 1 in
      (args, params, map (\case
        (Jump i, vs) -> (Jump (i + offset), vs)
        (Cond f i, vs) -> (Cond f (i + offset), vs)
        c -> c) is)

    organize pn = do
      (c, s, m) <- get
      if pn `elem` s then return ()
      else case M.lookup pn ps of
        Nothing -> return ()
        Just (inputs, outputs, insts) -> do
          let endOfProc = c + toInteger (length insts) - 1
          put (endOfProc, S.insert pn s, M.insert pn (endOfProc, inputs, outputs) m)
          mapM_ (\case
            (Call pn' _ _, []) -> organize pn'
            _ -> return ()) insts

instsToGraph :: Map ProcName (Integer, [Var], [Var]) -> Imp -> Graph Loc Edge Inst
instsToGraph callM cs = prune $ G.fromLists verts edges
  where
    endProg = toInteger $ length cs - 1
    verts = tail $
      zipWith vertOf [0..] (map snd cs) ++ [(Loc endProg, Inst (Loc endProg) [] (LBool True))]
    edges = concat $ zipWith edgesOf [0..] cs

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
            let prelocs = case l of
                        0 -> [Loc l']
                        n -> [Loc n, Loc l'] in
            [ (G.HEdge (S.fromList prelocs) (Loc (l+1))
            , Leaf $ manyAnd
                [ groupUp (inputs & vars %~ setLoc l)
                          (map V inps & vars %~ setLoc l')
                , groupUp (map V outputs & vars %~ setNew & vars %~ setLoc (l+1))
                          (map V outs & vars %~ setLoc l')
                , varCarry l (l+1) (filter (`notElem` outs) vs)
                ])
            ]
      Done -> []

      Store objref valref obj val ->
        let obj' = (obj & vars %~ setLoc l)
            val' = (val & vars %~ setLoc l)
            vs' = filter (\v -> v /= objref && v /= valref) vs
        in
        [ second LOnly $ edgeFrom l (l+1)
          ( manyAnd
            [ varCarry l (l+1) vs'
            , mkEql (T.typeOf objref) (V $ setNew $ setLoc (l+1) objref) obj'
            , mkEql (T.typeOf valref) (V $ setNew $ setLoc (l+1) valref) val'
            ]) ]
      Load ref _ obj ->
        let obj' = (obj & vars %~ setLoc l)
            vs' = filter (/= ref) vs
        in
        [ second ROnly $ edgeFrom l (l+1) (varCarry l (l+1) vs' `mkAnd`
              mkEql (T.typeOf ref) (V $ setNew $ setLoc (l+1) ref) obj') ]

    setLoc l v = v & varLoc .~ l
    setNew v = v & varNew .~ True
    edgeFrom l l' e =
      if l == 0
      then (G.HEdge S.empty (Loc l'), Leaf e)
      else (G.HEdge (S.singleton (Loc l)) (Loc l'), Leaf e)

    varCarry l l' vs =
      let bef = vs & map (setLoc l)
          aft = vs & map (setLoc l') & map setNew
      in groupUp (map V bef) (map V aft)

    groupUp as bs = manyAnd $ zipWith (\a b -> mkEql (T.typeOf a) a b) as bs
