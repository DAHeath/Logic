module Grammar.Simplify where

import           Control.Lens

import           Data.Foldable
import qualified Data.Set as S
import qualified Data.Map as M

import           Formula hiding (Rule)

import           Grammar.Grammar

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

    cleanUp (Rule cats lhs f ps) =
      Rule cats lhs (varElim (varSet lhs `S.union` varSet ps) f) ps

inline :: MonadVocab m => Grammar -> m Grammar
inline (Grammar start rs) = do
  let toInline = S.filter (\inst -> inst /= start && cardinality inst rs == 1) (instances rs)
  rs' <- foldrM (\inst rs' -> inlineRule (head $ rulesFor inst rs') rs') rs toInline
  pure (Grammar start rs')

-- | Substitute occurrences of the rule left hand side instance with the body of the rule.
inlineRule :: MonadVocab m => Rule -> [Rule] -> m [Rule]
inlineRule (Rule _ lhs body rhs) g =
  delete sym <$> mapM (\(Rule cats lhs' f rhs') -> uncurry (Rule cats lhs') <$> repRHS (f, rhs')) g
  where
    sym = lhs ^. productionSymbol
    repRHS (f, ps) = repRHS' ([], f, ps)
    repRHS' (acc, f, p:ps) =
      if (p ^. productionSymbol) == sym
      then do
        (f', ps') <- freshen (M.fromList $ zip (lhs ^. productionVars ) (p ^. productionVars)) (body, rhs)
        repRHS' (ps' ++ acc, mkAnd f f', ps)
      else repRHS' (p : acc, f, ps)
    repRHS' (acc, f, []) = pure (f, acc)

disjoin :: Grammar -> Grammar
disjoin (Grammar start rs)  = Grammar start $ foldr disjoinCandidate rs candidates
  where
    disjoinCandidate rs' g' = disjoinRules rs' : filter (`notElem` rs') g'
    candidates = M.elems (M.filter (\rs' -> length rs' > 1) instMap)
    -- a map from all instances in a rule to corresponding rules
    instMap = foldr addInstEntry M.empty rs
    addInstEntry r@(Rule ct lhs _ rhs) =
      M.insertWith (++) (ct, map (view productionSymbol) (lhs : rhs)) [r]

disjoinRules :: [Rule] -> Rule
disjoinRules rules =
  let rs = map rename rules in
  first & ruleBody .~ manyOr (map _ruleBody rs)
  where
    prodVars r = concatMap _productionVars (_ruleLHS r : _ruleRHS r)
    first = head rules
    rename r =
      let m = M.fromList (zip (prodVars r) (prodVars first))
      in subst m r
