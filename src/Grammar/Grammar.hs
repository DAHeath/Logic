module Grammar.Grammar where

import           Control.Lens

import           Data.Data (Data)
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Text.Prettyprint.Doc

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
cardinality cinst = length . filter (\r -> _productionSymbol (_ruleLHS r) == cinst)

instances :: [Rule] -> Set Symbol
instances = S.fromList . map (_productionSymbol . _ruleLHS)

-- | Delete the rules for the instance.
delete :: Symbol -> [Rule] -> [Rule]
delete cinst = filter (\r -> _productionSymbol (_ruleLHS r) /= cinst)

-- | Collect the rules whose nonterminal match the predicate.
rulesFor :: Symbol -> [Rule] -> [Rule]
rulesFor cinst = filter (\r -> _productionSymbol (_ruleLHS r) == cinst)
