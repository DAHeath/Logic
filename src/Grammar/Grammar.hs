module Grammar.Grammar where

import           Control.Lens
import           Control.Monad.State

import           Data.Data (Data)
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Text.Prettyprint.Doc
import           Data.List (nub)

import Logic.Formula hiding (Rule)

-- An identifier which should be completely unique per location.
type Symbol = Int

data Production = Production
  { _productionSymbol :: Symbol
  , _productionVars :: [Var]
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Production

-- It is crucial that every variable in a production location over a rule is unique.
data Rule = Rule
  { _ruleLHS :: Production
  , _ruleBody :: Form
  , _ruleRHS :: [Production]
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Rule

data Grammar = Grammar
  { _grammarStart :: Symbol
  , _grammarRules :: [Rule]
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Grammar

instance Pretty Grammar where
  pretty (Grammar start rs) = pretty start <> pretty "\n" <> vsep (map pretty rs)

-- An identifier which groups different instances of the same production location.
type ControlID = Int

instance Pretty Production where
  pretty (Production sym vs) = pretty sym <> pretty vs

instance Pretty Rule where
  pretty (Rule lhs body rhs) = pretty lhs <> pretty ": " <> pretty body <> pretty " | " <> pretty rhs

cardinality :: Symbol -> [Rule] -> Int
cardinality sym = length . filter (\r -> _productionSymbol (_ruleLHS r) == sym)

instances :: [Rule] -> Set Symbol
instances = S.fromList . map (_productionSymbol . _ruleLHS)

-- | Delete the rules for the instance.
delete :: Symbol -> [Rule] -> [Rule]
delete sym = filter (\r -> _productionSymbol (_ruleLHS r) /= sym)

-- | Collect the rules whose nonterminal match the predicate.
rulesFor :: Symbol -> [Rule] -> [Rule]
rulesFor sym = filter (\r -> _productionSymbol (_ruleLHS r) == sym)

rulesWith :: Symbol -> [Rule] -> [Rule]
rulesWith sym = filter (\r -> sym `elem` map (view productionSymbol) (r ^. ruleRHS))

type Clones = [Set Symbol]

clone :: Symbol -> Symbol -> Clones -> Clones
clone i j (cs:css) = if i `elem` cs then S.insert j cs:css else cs:clone i j css
clone i j [] = [S.fromList [i, j]]

cloneFor :: Symbol -> Clones -> Maybe (Set Symbol)
cloneFor i (cs:css) = if i `elem` cs then Just cs else cloneFor i css
cloneFor i [] = Nothing

predecessors :: Grammar -> Symbol -> Set Symbol
predecessors g s =
  S.fromList $ concatMap (map
    (view productionSymbol) . view ruleRHS) (rulesFor s (g ^. grammarRules))

successors :: Grammar -> Symbol -> Set Symbol
successors g s =
  S.fromList $ map (view (ruleLHS . productionSymbol)) (rulesWith s (g ^. grammarRules))

descendants :: Grammar -> Symbol -> Set Symbol
descendants g s = evalState (desc s) S.empty
  where
    desc :: Symbol -> State (Set Symbol) (Set Symbol)
    desc sym = do
      visited <- get
      if sym `elem` visited
      then return S.empty
      else do
        modify (S.insert sym)
        let ss = successors g sym
        ss' <- mapM desc (S.toList ss)
        return (S.unions $ ss : ss')
