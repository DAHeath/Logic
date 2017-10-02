{-# LANGUAGE LambdaCase, DeriveDataTypeable, FlexibleContexts #-}
module Language.Imperative where

import           Logic.Type as T
import           Logic.Formula
import           Logic.Chc

import           Control.Monad.State

import           Data.Data (Data)
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Map (Map)
import qualified Data.Map as M

import qualified Data.Graph.Inductive.Graph as G
import           Data.Graph.Inductive.PatriciaTree
import           Data.Graph.Inductive.Extras

import           Text.PrettyPrint.HughesPJClass
import qualified Data.GraphViz as GV
import qualified Data.Text.Lazy.IO as TIO

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
  deriving (Show, Eq, Ord, Data)

-- | The right hand side of an assignment.
data RHS
  = Expr Form
  | Arbitrary Type
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
  deriving (Show, Eq, Ord, Data)

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
  evalState (do
    i <- initial
    f <- commGraph' comm
    terminate (f i)) (0, M.empty)
  where
    commGraph' :: Comm -> State (Lbl, Map Int Lbl) (PartGraph -> PartGraph)
    commGraph' comm'
      | isSimple comm' = return $ \(PartGraph g n s) -> PartGraph g n (semSeq (commSem comm') s)
      | otherwise = case comm' of
        Seq c1 c2 -> do
          f1 <- commGraph' c1
          f2 <- commGraph' c2
          return (f1 . f2)
        Case e c1 c2 -> do
          f1 <- commGraph' c1
          f2 <- commGraph' c2
          h <- vert
          return $ \pg ->
            let (PartGraph g1 n1 s1) = f1 pg
                (PartGraph g2 n2 s2) = f2 pg
                g = G.insEdge (h, n1, semSeq (SemPredicate e) s1)
                  $ G.insEdge (h, n2, semSeq (SemPredicate (Apply Not e)) s2)
                  $ G.insNode (h, ())
                  $ overlay g1 g2
            in PartGraph g h SemSkip
        Loop e c -> do
          h <- vert
          f <- commGraph' c
          return $ \(PartGraph g en s) ->
            let PartGraph g' en' s' = f (PartGraph (G.insNode (h, ()) G.empty) h SemSkip)
                g'' = G.insEdge (h, en', semSeq (SemPredicate e) s') g'
            in PartGraph
              ( G.insEdge (h, en, semSeq (SemPredicate (Apply Not e)) s)
              $ overlay g g'')
              h SemSkip
        Skip -> return id
        Jump l -> do
          v <- lblVert l
          return $ \(PartGraph g _ _) ->
            PartGraph (G.insNode (v, ()) g) v SemSkip
        Lbl l c -> do
          v <- lblVert l
          f <- commGraph' c
          return $ \g ->
            let PartGraph g' en s = f g
            in PartGraph ( G.insEdge (v, en, s)
                         $ G.insNode (v, ())
                         $ g'
                         ) v SemSkip
        _ -> return $ \(PartGraph g n s) -> PartGraph g n (SemSeq (commSem comm') s)
    lblVert l = do
      m <- snd <$> get
      case M.lookup l m of
        Just v -> return v
        Nothing -> do
          v <- vert
          let m' = M.insert l v m
          modify (\(v', _) -> (v', m'))
          return v
    vert = do
      v <- fst <$> get
      modify (\(_, m) -> (v+1, m))
      return v
    initial = do
      v <- vert
      return (PartGraph (G.insNode (v, ()) G.empty) v SemSkip)
    terminate (PartGraph g en s) = do
      if s == SemSkip then return g
      else do
        v <- vert
        return $ G.insEdge (v, en, s)
               $ G.insNode (v, ())
               $ g

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

instance Pretty RHS where
  pPrint = \case
    Expr f -> pPrint f
    Arbitrary t -> text "ANY" <+> pPrint t

instance Pretty SemAct where
  pPrint = \case
    SemSeq a1 a2    -> pPrint a1 <> text ";" $+$ pPrint a2
    SemAss v r      -> hsep [pPrint v, text ":=", pPrint r]
    SemPredicate e  -> pPrint e
    SemCase e c1 c2 -> (text "IF" <+> pPrint e) $+$ nest 2 (pPrint c1) $+$
                       text "ELSE" $+$ nest 2 (pPrint c2)
    SemSkip         -> text "SKIP"

display :: FilePath -> Gr () SemAct -> IO ()
display fn g =
  let g' = G.nmap prettyShow $ G.emap prettyShow g
      params = GV.nonClusteredParams { GV.fmtNode = \ (n,l)  -> [GV.toLabel (show n ++ ": " ++ l)]
                                     , GV.fmtEdge = \ (_, _, l) -> [GV.toLabel l]
                                     }
      dot = GV.graphToDot params g'
  in TIO.writeFile fn (GV.printDotGraph dot)
