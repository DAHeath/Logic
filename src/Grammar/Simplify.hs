module Grammar.Simplify where

import           Control.Lens

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
simplify :: MonadVocab m => Grammar -> m Grammar
simplify = fmap (over grammarRules (map cleanUp)) . loop
  where
    loop g = do
      g' <- disjoin <$> inline g
      if g' == g then pure g' else loop g'

    cleanUp (Rule lhs f ps) =
      Rule lhs (varElim (varSet lhs `S.union` varSet ps) f) ps

inline :: MonadVocab m => Grammar -> m Grammar
inline (Grammar start rs) = do
  let toInline = S.filter (\inst -> inst /= start && cardinality inst rs == 1) (instances rs)
  rs' <- foldrM (\inst rs' -> inlineRule (head $ rulesFor inst rs') rs') rs toInline
  pure (Grammar start rs')

-- | Substitute occurrences of the rule left hand side instance with the body of the rule.
inlineRule :: MonadVocab m => Rule -> [Rule] -> m [Rule]
inlineRule (Rule lhs body rhs) g =
  delete sym <$> mapM (\(Rule lhs' f rhs') -> uncurry (Rule lhs') <$> repRHS (f, rhs')) g
  where
    sym = _productionSymbol lhs
    repRHS (f, ps) = repRHS' ([], f, ps)
    repRHS' (acc, f, p:ps) =
      if _productionSymbol p == sym
      then do
        (f', ps') <- freshen (M.fromList $ zip (_productionVars lhs) (_productionVars p)) (body, rhs)
        repRHS' (ps' ++ acc, mkAnd f f', ps)
      else repRHS' (p : acc, f, ps)
    repRHS' (acc, f, []) = pure (f, acc)

disjoin :: Grammar -> Grammar
disjoin (Grammar start rs)  = Grammar start $ foldr disjoinCandidate rs candidates
  where
    disjoinCandidate rs g' = disjoinRules rs : filter (`notElem` rs) g'
    candidates = M.elems (M.filter (\rs -> length rs > 1) instMap)
    -- a map from all instances in a rule to corresponding rules
    instMap = foldr addInstEntry M.empty rs
    addInstEntry r@(Rule lhs _ rhs) =
      M.insertWith (++) (_productionSymbol lhs : map _productionSymbol rhs) [r]

disjoinRules :: [Rule] -> Rule
disjoinRules rules =
  let rs = map rename rules in
  Rule (_ruleLHS first) (manyOr (map _ruleBody rs)) (_ruleRHS first)
  where
    prodVars r = concatMap _productionVars (_ruleLHS r : _ruleRHS r)
    first = head rules
    rename r =
      let m = M.fromList (zip (prodVars r) (prodVars first))
      in subst m r
