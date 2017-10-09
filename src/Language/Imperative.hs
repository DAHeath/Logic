{-# LANGUAGE LambdaCase, DeriveDataTypeable, FlexibleContexts #-}
module Language.Imperative where

import           Control.Monad.State

import           Data.Data (Data)
import           Data.Tuple (swap)
import qualified Data.Graph.Inductive.Graph as G
import           Data.Graph.Inductive.PatriciaTree
import           Data.Graph.Inductive.Extras
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Map (Map)
import qualified Data.Map as M

import           Logic.Type as T
import           Logic.Formula
import           Logic.Var
import           Logic.Chc

import           Text.PrettyPrint.HughesPJClass

-- | The space of imperative programs are represented as inductively constructed
-- commands.
data Comm
  = Seq Comm Comm
  | Case Form Comm Comm
  | Loop Form Comm
  | Ass Var RHS
  | Skip
  | Lbl Int Comm
  | Jump Int
  | Store Name Form Form
  deriving (Show, Eq, Ord, Data)

-- | The right hand side of an assignment.
data RHS
  = Expr Form
  | Arbitrary Type
  | Select Name Form
  deriving (Show, Eq, Ord, Data)

commChc :: Comm -> [Chc]
commChc = undefined

type Lbl = Int

-- | Semantic actions of a program which can be represented as a single logical
-- formula. This is limited to combinations of conditionals and assignments.
data SemAct
  = SemSeq SemAct SemAct
  | SemAss Var RHS
  | SemCase Form SemAct SemAct
  | SemSkip
  | SemPredicate Form
  | SemStore Name Form Form
  deriving (Show, Eq, Ord, Data)

semantics :: SemAct -> (Form, Map Var Var)
semantics ac = let (f, (m, _)) = runState (sem ac) (M.empty, S.empty)
               in (f, m)
  where
    sem = \case
      SemSeq a1 a2 -> mkAnd <$> sem a1 <*> sem a2
      SemAss v rhs -> do
        (m, s) <- get
        let v' = fresh s v
        e <- case rhs of
          Arbitrary _ -> return (LBool True)
          Expr e' -> do
            let e'' = subst m e'
            return (app2 (Eql $ typeOf v') (V v') e'')
          Select{} ->
            -- Select statements cannot translated to formulas.
            return (LBool False)
        put (M.insert v v' m, S.insert v' s)
        return e
      SemCase e a1 a2 -> do
        (m, s) <- get
        let e' = subst m e
        sem1 <- sem a1
        (m1, s1) <- get
        put (m, s)
        sem2 <- sem a2
        (m2, s2) <- get
        let (m1', as1) = mergeBranch s2 s1 m2 m1
        let sem1' = mkAnd sem1 as1
        let (_  , as2) = mergeBranch s1 s2 m1 m2
        let sem2' = mkAnd sem2 as2
        put (m1', S.union s1 s2)
        return (appMany (If T.Bool) [e', sem1', sem2'])
      SemSkip         -> return (LBool True)
      SemPredicate e  -> do
        (m, _) <- get
        return $ subst m e
      SemStore{} ->
        -- Store statements cannot translated to formulas.
        return (LBool False)

    -- | On if branches, one branch might alias a variable more than the other.
    -- To account for this, we decide how to update the variables after the
    -- semantic action of the branch.
    mergeBranch s1 s2 m1 m2 =
      let updateNeeded = S.toList $ s1 S.\\ s2
          invM1 = M.fromList $ map swap $ M.toList m1
          originals = map (subst invM1) updateNeeded
          branched = map (subst m2) originals
          eqs = zipWith (\v1 v2 -> app2 (Eql (typeOf v1)) (V v1) (V v2)) updateNeeded branched
          m1' = foldr (\(v1, v2) m -> M.insert v1 v2 m) m1 (zip originals branched)
      in (m1', manyAnd eqs)

semSeq :: SemAct -> SemAct -> SemAct
semSeq SemSkip s = s
semSeq s SemSkip = s
semSeq s1 s2 = SemSeq s1 s2

-- | `simple` commands are those which can appear directly as a semantic
-- action.
isSimple :: Comm -> Bool
isSimple = \case
  Seq c1 c2    -> isSimple c1 && isSimple c2
  Case _ c1 c2 -> isSimple c1 && isSimple c2
  Loop _ _     -> False
  Lbl _ _      -> False
  Jump _       -> False
  Ass _ _      -> True
  Skip         -> True
  Store{}      -> True

-- | Convert a command to a semantic action. Only a subset of commands are
-- convertible to semantic actions, any in general full commands should be
-- converted to structured actions.
commSem :: Comm -> SemAct
commSem = \case
  Seq c1 c2    -> semSeq (commSem c1) (commSem c2)
  Case e c1 c2 -> SemCase e (commSem c1) (commSem c2)
  Ass v e      -> SemAss v e
  Loop _ _     -> SemSkip
  Lbl _ _      -> SemSkip
  Jump _       -> SemSkip
  Skip         -> SemSkip
  Store f i v  -> SemStore f i v

-- | A flow graph presents the semantic actions of the program as vertices with
-- transition formulas on the edges. The semantic actions are labelled with the
-- variables that are live at the end of the semantic action.
data FlowGr = FlowGr
  { getFlowGr :: Gr (Set Var) SemAct
  , entrance :: G.Node
  , exit :: G.Node
  }

data PartGraph = PartGraph (Gr () SemAct) G.Node SemAct

commGraph :: Comm -> Gr () SemAct
commGraph comm =
  renumber $ evalState (do
    i <- initial
    f <- commGraph' comm i
    terminate f) (0, M.empty)
  where
    commGraph' :: Comm -> PartGraph -> State (Lbl, Map Int Lbl) PartGraph
    commGraph' comm' pg@(PartGraph g n s)
      | isSimple comm' = return $ PartGraph g n (semSeq (commSem comm') s)
      | otherwise = case comm' of
        Seq c1 c2 -> commGraph' c2 pg >>= commGraph' c1
        Case e c1 c2 -> do
          (PartGraph g1 n1 s1) <- commGraph' c1 pg
          (PartGraph g2 n2 s2) <- commGraph' c2 pg
          h <- vert
          let g' = G.insEdge (h, n1, semSeq (SemPredicate e) s1)
                 $ G.insEdge (h, n2, semSeq (SemPredicate (Not :@ e)) s2)
                 $ G.insNode (h, ())
                 $ overlay g1 g2
          return $ PartGraph g' h SemSkip
        Loop e c -> do
          h <- vert
          (PartGraph g' en' s') <- commGraph' c (PartGraph (G.insNode (h, ()) G.empty) h SemSkip)
          let g'' = G.insEdge (h, en', semSeq (SemPredicate e) s') g'
          return $ PartGraph
              ( G.insEdge (h, n, semSeq (SemPredicate (Not :@ e)) s)
              $ overlay g g'')
              h SemSkip
        Skip -> return pg
        Jump l -> skipTo g <$> lblVert l
        Lbl l c -> do
          v <- lblVert l
          (PartGraph g' en s') <- commGraph' c pg
          return $ PartGraph ( G.insEdge (v, en, s')
                             $ G.insNode (v, ()) g'
                             ) v SemSkip
        _ -> return $ PartGraph g n (semSeq (commSem comm') s)
    lblVert l = do
      m <- snd <$> get
      case M.lookup l m of
        Just v -> return v
        Nothing -> do
          v <- vert
          modify (\(v', _) -> (v', M.insert l v m))
          return v
    vert = state (\(v, m) -> (v, (v+1, m)))
    initial = skipTo G.empty <$> vert
    skipTo g n = PartGraph (G.insNode (n, ()) g) n SemSkip
    terminate (PartGraph g en s) =
      if s == SemSkip then return g
      else do
        v <- vert
        return $ G.insEdge (v, en, s) $ G.insNode (v, ()) g
    renumber :: Gr () a -> Gr () a
    renumber g =
      let n = G.noNodes g
          ren = M.fromList (zip [n-1,n-2..0] [0..n-1])
          adj (b, n') = (b, M.findWithDefault (-1) n' ren)
      in
      G.gmap (\(bef, n', a, aft) ->
        (map adj bef, M.findWithDefault (-1) n' ren, a, map adj aft)) g

instance Pretty Comm where
  pPrint = \case
    Seq c1 c2    -> pPrint c1 $+$ pPrint c2
    Case e c1 c2 -> (text "IF" <+> pPrint e) $+$ nest 2 (pPrint c1) $+$
                    text "ELSE" $+$ nest 2 (pPrint c2)
    Loop e c     -> (text "WHILE" <+> pPrint e) $+$ nest 2 (pPrint c)
    Ass v r      -> hsep [pPrint v, text ":=", pPrint r]
    Skip         -> text "SKIP"
    Lbl l c      -> text ("LABEL: " ++ show l) $+$ pPrint c
    Jump l       -> text ("JUMP: " ++ show l)
    Store f i v  -> hsep [text "STORE", text f, pPrint i, pPrint v]

instance Pretty RHS where
  pPrint = \case
    Expr f -> pPrint f
    Arbitrary t -> text "ANY" <+> pPrint t
    Select f i -> hsep [text "SELECT", text f, pPrint i]

instance Pretty SemAct where
  pPrint = \case
    SemSeq a1 a2    -> pPrint a1 <> text ";" $+$ pPrint a2
    SemAss v r      -> hsep [pPrint v, text ":=", pPrint r]
    SemPredicate e  -> pPrint e
    SemCase e c1 c2 -> (text "IF" <+> pPrint e) $+$ nest 2 (pPrint c1) $+$
                       text "ELSE" $+$ nest 2 (pPrint c2)
    SemSkip         -> text "SKIP"
    SemStore f i v  -> hsep [text "STORE", text f, pPrint i, pPrint v]
