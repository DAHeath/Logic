module Grammar.Simplify where

import           Data.Foldable
import           Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Map as M

import Logic.Formula hiding (Rule)

import Grammar.Grammar

-- | There are two ruels for logical grammar simplification:
-- If there is a nonterminal with cardinality one (that is non-recursive), inline the body
-- at all occurrences, deleting the rule for the nonterminal (the start symbol cannot be inlined).
-- If there is a nonterminal with multiple rules that share the same nonterminals in the body,
-- disjoin them into a single rule.
-- Repeat the rules into no more reductions are possible.
simplify :: MonadVocab m => ControlInst -> Grammar -> m Grammar
simplify start = fmap (map cleanUp) . loop
  where
    loop g = do
      g' <- disjoin <$> inline start g
      if g' == g then pure g' else loop g'

    cleanUp (Rule lhs (RHS f ps)) =
      Rule lhs (RHS (varElim (varSet lhs `S.union` varSet ps) f) ps)

inline :: MonadVocab m => ControlInst -> Grammar -> m Grammar
inline start g = do
  let toInline = S.filter (\inst -> inst /= start && cardinality inst g == 1) (instances g)
  foldrM (\inst g' -> inlineRule (head $ rulesFor inst g') g') g toInline

-- | Substitute occurrences of the rule left hand side instance with the body of the rule.
inlineRule :: MonadVocab m => Rule -> Grammar -> m Grammar
inlineRule (Rule lhs rhs) g =
  delete cinst <$> mapM (\(Rule lhs' rhs') -> Rule lhs' <$> repRHS rhs') g
  where
    cinst = controlID lhs
    repRHS (RHS f ps) = repRHS' ([], f, ps)
    repRHS' (acc, f, p:ps) =
      if controlInst p == cinst
      then do
        RHS f' ps' <- freshen (M.fromList $ zip (controlVars lhs) (controlVars p)) rhs
        repRHS' (ps' ++ acc, mkAnd f f', ps)
      else repRHS' (p : acc, f, ps)
    repRHS' (acc, f, []) = pure $ RHS f acc

disjoin :: Grammar -> Grammar
disjoin g = foldr disjoinCandidate g candidates
  where
    disjoinCandidate rs g' = disjoinRules rs : filter (`notElem` rs) g'
    candidates = M.elems (M.filter (\rs -> length rs > 1) instMap)
    -- a map from all instances in a rule to corresponding rules
    instMap = foldr addInstEntry M.empty g
    addInstEntry r@(Rule lhs rhs) =
      M.insertWith (++) (controlInst lhs : map controlInst (rhsProductions rhs)) [r]

disjoinRules :: [Rule] -> Rule
disjoinRules rules =
  let rs = map rename rules in
  Rule (ruleLHS first) (RHS (manyOr (bodies rs)) (rhsProductions $ ruleRHS first))
  where
    bodies = map (rhsConstraint . ruleRHS)
    prodVars r = concatMap controlVars (ruleLHS r : productions r)
    first = head rules
    rename r =
      let m = M.fromList (zip (prodVars r) (prodVars first))
      in subst m r

