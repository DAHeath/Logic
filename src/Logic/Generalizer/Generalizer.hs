{-# LANGUAGE QuasiQuotes #-}
import Logic.Formula
import Logic.Formula.Parser

-- | Determine if variables x/y are linearly related
linearlyRelated :: Var -> Var -> Form
linearlyRelated x y =
  [form| not (a:Int = 0)
      && not (b:Int = 0)
      && (a:Int * @x:Int + b:Int * @y:Int = c:Int)|]

modularCongruence :: Var -> Form
modularCongruence x =
  [form| a:Int > 1
      && @x:Int % a:Int = b:Int|]

-- | Given a list of formulas, attempt to find generalizations which capture the
-- semantics of all formulas. In other words, a generalization `g` exists if
-- for all formulas f, f => g.
generalize :: [Form] -> [Form]
generalize = undefined
