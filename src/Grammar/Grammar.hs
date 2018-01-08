module Grammar.Grammar where

import           Data.Foldable
import           Data.Data (Data)
import           Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Map as M
import           Data.Text.Prettyprint.Doc

import Logic.Formula hiding (Rule)

-- An identifier which should be completely unique per location.
type ControlInst = Int

-- An identifier which groups different instances of the same control location.
type ControlID = Int

data ControlLocation = ControlLocation
  { controlInst :: ControlInst
  , controlID :: ControlID
  , controlVars :: [Var]
  } deriving (Show, Read, Eq, Ord, Data)

instance Pretty ControlLocation where
  pretty (ControlLocation inst id vs) =
    pretty id <> pretty "(" <> pretty inst <> pretty ")" <> pretty vs

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

cardinality :: ControlInst -> Grammar -> Int
cardinality cinst = length . filter (\r -> controlInst (ruleLHS r) == cinst)

instances :: Grammar -> Set ControlInst
instances = S.fromList . map (controlInst . ruleLHS)

-- | Delete the rules for the instance.
delete :: ControlInst -> Grammar -> Grammar
delete cinst = filter (\r -> controlInst (ruleLHS r) /= cinst)

-- | Collect the rules whose nonterminal match the predicate.
rulesFor :: ControlInst -> Grammar -> [Rule]
rulesFor cinst = filter (\r -> controlInst (ruleLHS r) == cinst)

productions :: Rule -> [ControlLocation]
productions = rhsProductions . ruleRHS

type Grammar = [Rule]

-- interpolate
-- inductive
-- unwind
-- nonrecursive

-- -- | Find the corresponding non-recursive grammar from the given start symbol.
-- -- That is, remove all productions which contain nonterminals which have already
-- -- been seen.
-- nonrecursive :: (Rule p s -> Rule p s -> Bool) -> (p -> p -> Bool) -> p -> Grammar p s -> Grammar p s
-- nonrecursive matchRule matchNT start g =
--   let toDelete = execState (recNT [start] start) [] in
--   foldr (delete . matchRule) g toDelete
--   where
--     recNT seen nt = mapM_ (recRule seen) (rulesFor (matchNT nt) g)
--     -- If we've seen any of the nonterminals in the rule before, add the rule to be
--     -- deleted. Otherwise recurse with the lhs marked as seen.
--     recRule seen (Rule lhs rhs) =
--       if or [matchNT nt nt' | nt <- seen, nt' <- nonterminals rhs]
--       then modify (Rule lhs rhs:)
--       else mapM_ (recNT (lhs:seen)) (nonterminals rhs)
--
