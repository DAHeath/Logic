module Grammar.Grammar where

import           Data.Data (Data)
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Text.Prettyprint.Doc

import Logic.Formula hiding (Rule)

-- An identifier which should be completely unique per location.
type Symbol = Int

-- An identifier which groups different instances of the same control location.
type ControlID = Int

data ControlLocation = ControlLocation
  { controlSymbol :: Symbol
  , controlID :: ControlID
  , controlVars :: [Var]
  } deriving (Show, Read, Eq, Ord, Data)

instance Pretty ControlLocation where
  pretty (ControlLocation inst iden vs) =
    pretty iden <> pretty "(" <> pretty inst <> pretty ")" <> pretty vs

-- It is crucial that every variable in a control location over a rule is unique.
data Rule = Rule
  { ruleLHS :: ControlLocation
  , ruleRHS :: RHS
  } deriving (Show, Read, Eq, Ord, Data)

instance Pretty Rule where
  pretty (Rule lhs rhs) = pretty lhs <> pretty ": " <> pretty rhs

data RHS = RHS
  { rhsConstraint :: Form
  , rhsProductions :: [ControlLocation]
  } deriving (Show, Read, Eq, Ord, Data)

instance Pretty RHS where
  pretty (RHS cons prods) = pretty cons <> pretty " | "  <> pretty prods

cardinality :: Symbol -> Grammar -> Int
cardinality cinst = length . filter (\r -> controlSymbol (ruleLHS r) == cinst)

instances :: Grammar -> Set Symbol
instances = S.fromList . map (controlSymbol . ruleLHS)

-- | Delete the rules for the instance.
delete :: Symbol -> Grammar -> Grammar
delete cinst = filter (\r -> controlSymbol (ruleLHS r) /= cinst)

-- | Collect the rules whose nonterminal match the predicate.
rulesFor :: Symbol -> Grammar -> [Rule]
rulesFor cinst = filter (\r -> controlSymbol (ruleLHS r) == cinst)

productions :: Rule -> [ControlLocation]
productions = rhsProductions . ruleRHS

type Grammar = [Rule]

-- interpolate
-- inductive
