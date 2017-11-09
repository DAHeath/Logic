{-# LANGUAGE TemplateHaskell, ConstraintKinds #-}

module Logic.Solver.Z3 where

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Reader

import           Data.List (partition)
import           Data.List.Split (splitOn)
import           Data.Maybe
import qualified Data.Map as M
import           Data.Map (Map)
import qualified Data.Tree as Tr
import           Data.Tree (Tree)

import           Logic.Chc (Chc)
import qualified Logic.Chc as C
import           Logic.Formula (Form((:@)))
import qualified Logic.Formula as F
import           Logic.Var
import           Logic.Type (Type((:=>)))
import qualified Logic.Type as T
import qualified Logic.Model as M

import           Text.Read (readMaybe)

import           Z3.Monad hiding (local)

data Env = Env { _envVars :: Map Var AST
               , _envFuns :: Map Var FuncDecl
               } deriving (Show, Eq, Ord)

makeLenses ''Env

type SMT m = (MonadState Env m, MonadZ3 m)

-- | Invoke `duality` to solve the relational post fixed-point problem.
solveChc :: MonadIO m => [Chc] -> m (Either M.Model M.Model)
solveChc hcs = runEnvZ3 sc
  where
    sc =
      let (queries, rules) = partition C.isQuery hcs
          qids = map (const "q") queries
          qs = zipWith mkQuery queries qids
          satForms = map F.toForm rules ++ qs
          rids = map (\n -> "RULE" ++ show n) [0..length hcs-1]
      in do
        useDuality
        forms <- traverse formToAst satForms
        rids' <- traverse mkStringSymbol rids
        zipWithM_ fixedpointAddRule forms rids'

        let quers = [Free ["q"] 0 T.Bool]
        quers' <- traverse funcToDecl quers
        res <- fixedpointQueryRelations quers'
        case res of
          Unsat -> Right <$> (modelToModel =<< fixedpointGetModel)
          _     -> Left <$> (modelToModel =<< fixedpointGetRefutation)

    mkQuery q n =
      let theQuery = F.V $ Free [n] 0 T.Bool in
      F.app2 F.Impl (F.mkNot $ F.toForm q) theQuery

    useDuality = do
      pars <- mkParams
      join $ paramsSetSymbol pars <$> mkStringSymbol "engine" <*> mkStringSymbol "duality"
      fixedpointSetParams pars

-- | Given some formulas, determine if the conjunction of the formulas is satisfiable.
-- If it is not, find some minimal set such that removing any additional formulas from
-- the set is satisfiable.
unsatCore :: MonadIO m => [Form] -> m (Maybe [Form])
unsatCore = fixedM z3Core
  where
    fixedM :: (Eq a, Monad m) => (a -> m (Maybe a)) -> a -> m (Maybe a)
    fixedM f x =
      maybe
        (return Nothing)
        (\x' -> if x' == x then return (Just x') else fixedM f x') =<< f x

    z3Core fs = runEnvZ3 $ do
      let labels = map (\i -> "LABEL" ++ show i) [0..length fs - 1]
      lbls <- traverse (\l -> join $ mkConst <$> mkStringSymbol l <*> mkBoolSort) labels
      fs' <- traverse formToAst fs

      let m = zip lbls fs

      zipWithM_ solverAssertAndTrack fs' lbls
      res <- solverCheck
      case res of
        Unsat -> do lbls' <- solverGetUnsatCore
                    return $ Just $ mapMaybe (`lookup` m) lbls'
        _ -> return Nothing

-- | Find a satisfying model of an input formula (if one exists).
satisfy :: MonadIO m => Form -> m (Maybe M.Model)
satisfy f = runEnvZ3 $ do
  assert =<< formToAst f
  (_, m) <- solverCheckAndGetModel
  case m of
    Nothing -> return Nothing
    Just m' -> Just <$> modelToModel m'

-- | The the satisfiability of the input formula.
isSat :: MonadIO m => Form -> m Bool
isSat f = do
  sol <- runEnvZ3 sc
  case sol of
    Sat -> return True
    _   -> return False

  where sc = (assert =<< formToAst f) >> check

-- | Test the validity of the input formula.
isValid :: MonadIO m => Form -> m Bool
isValid f = runEnvZ3 $ do
  sol <- sc
  case sol of
    Unsat -> return True
    _     -> return False
  where sc = (assert =<< formToAst (F.mkNot f)) >> check

-- | Is `f -> g` a valid formula?
entails :: MonadIO m => Form -> Form -> m Bool
entails f g = isValid (F.app2 F.Impl f g)

-- | Construct a tree interpolant for a tree of formulas. The tree interpolant
-- is constructed such that:
--  + Each node formula conjoined with all child interpolants implies the node's
--    interpolant.
--  + The root node is contradicted.
--
--  Note that an interpolant tree is only constructed given that the original tree
--  of formulas is mutually unsatisfiable.
interpolate :: MonadIO m => Tree Form -> m (Either M.Model (Tree Form))
interpolate ftree = runEnvZ3 $ do
  -- The full formula needs an interpolant wrapper (which should generate the
  -- interpolant `false` if the input is unsatisfiable).
  t <- mkInterpolant =<< buildInterp ftree
  is <- computeInterpolant t =<< mkParams
  case is of
    Just (Right is') ->
      Right <$> (buildTree <$> traverse astToForm is' <*> pure ftree)
    Just (Left m) ->
      Left <$> modelToModel m
    _ -> undefined -- return Nothing
  where
    -- Z3 represents tree interpolants using the `mkInterpolant` wrapper for
    -- subformulas. `mkInterpolant` indicates that an interpolant for the
    -- marked subformula should be generated. To produce the correct tree,
    -- each child of the current node is marked for generating an interpolant.
    buildInterp (Tr.Node n cs) = do
      f <- formToAst n
      fs <- traverse (mkInterpolant <=< buildInterp) cs
      mkAnd (f : fs)

    -- Move the obtained interpolants into a tree which corresponds to the input.
    buildTree fs t = evalState (populate t) fs

    -- Z3 returns the interpolants as just a list. The interpolants are organized
    -- in postorder. `populate` will crash (`fromJust`) if the result contains
    -- fewer interpolants than the number of nodes in the input tree.
    populate (Tr.Node _ cs) =
      flip Tr.Node <$> traverse populate cs <*> state (fromJust . uncons)

simplify :: MonadIO m => Form -> m Form
simplify f = runEnvZ3 $ astToForm =<< Z3.Monad.simplify =<< formToAst f

superSimplify :: MonadIO m => Form -> m Form
superSimplify (F.LInt n) = return (F.LInt n)
superSimplify f = runEnvZ3 $ astToForm =<< superSimp =<< formToAst f
  where
    superSimp :: MonadZ3 m => AST -> m AST
    superSimp ast = do
      tac  <- join $ andThenTactic <$> mkTactic "propagate-values" <*> skipTactic
      tac' <- join $ andThenTactic <$> mkTactic "ctx-solver-simplify" <*> pure tac

      g <- mkGoal False False False
      goalAssert g ast
      rs <- getApplyResultSubgoals =<< applyTactic tac' g
      asts <- concat <$> mapM getGoalFormulas rs
      case asts of
        (f : _) -> return f
        _ -> return ast

-- | A monadic context for Z3 actions which caches the variables and functions
-- which have already been created. It also resolve DeBrujin indices which Z3
-- uses to represent variables.
newtype EnvZ3 a = EnvZ3 { getEnvZ3 :: StateT Env Z3 a }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadState Env
           , MonadIO
           )

instance MonadZ3 EnvZ3 where
  getSolver     = EnvZ3 $ lift getSolver
  getContext    = EnvZ3 $ lift getContext
  getFixedpoint = EnvZ3 $ lift getFixedpoint

runEnvZ3 :: MonadIO m => EnvZ3 a -> m a
runEnvZ3 ac = liftIO $ evalZ3 (evalStateT (getEnvZ3 ac') emptyEnv)
  where
    ac' = push *> ac <* reset
    emptyEnv = Env M.empty M.empty

-- | Convert the ADT formula to a Z3 formula.
formToAst :: SMT m => Form -> m AST
formToAst f =
  case f of
    F.V v               -> var v
    F.LUnit             -> undefined
    F.LBool True        -> mkTrue
    F.LBool False       -> mkFalse
    F.LInt l            -> mkInteger l
    F.LReal _           -> undefined
    f' :@ a             -> let (f'', as) = gatherApp f' [a]
                           in appToZ3 f'' as
    _ -> undefined
  where
    gatherApp :: Form -> [Form] -> (Form, [Form])
    gatherApp (f' :@ a) args = gatherApp f' (a : args)
    gatherApp x args = (x, args)

    register v = do
      fd <- varDec v
      fixedpointRegisterVariable fd
      v' <- mkApp fd []
      envVars %= M.insert v v'
      return v'

    var v = do
      env <- use envVars
      case M.lookup v env of
        Nothing -> register v
        Just v' -> return v'

-- | Convert a function application to a Z3 formula.
appToZ3 :: SMT m => Form -> [Form] -> m AST
appToZ3 f args =
  case f of
    F.V v        -> join $ mkApp <$> funcToDecl v <*> traverse formToAst args
    F.Not        -> mkNot =<< formToAst (head args)
    F.And        -> many mkAnd
    F.Or         -> many mkOr
    F.Add _      -> many mkAdd
    F.Mul _      -> many mkMul
    F.Sub _      -> many mkSub
    F.Distinct _ -> many mkDistinct
    F.Impl       -> two mkImplies
    F.Iff        -> two mkIff
    F.Div _      -> two mkDiv
    F.Mod _      -> two mkMod
    F.If _       -> three mkIte

    F.Eql _      -> two mkEq
    F.Lt _       -> two mkLt
    F.Le _       -> two mkLe
    F.Gt _       -> two mkGt
    F.Ge _       -> two mkGe

    F.Store _ _  -> three mkStore
    F.Select _ _ -> two mkSelect

    F.LUnit      -> undefined
    F.LBool b    -> mkBool b
    F.LInt _     -> undefined
    F.LReal _    -> undefined
    _ :@ _       -> undefined

  where
    many o = o =<< traverse formToAst args
    two o = join $ o <$> formToAst (head args) <*> formToAst (args !! 1)
    three o = join $ o <$> formToAst (head args)
                       <*> formToAst (args !! 1)
                       <*> formToAst (args !! 2)

funcToDecl :: (MonadState Env z3, MonadZ3 z3) => Var -> z3 FuncDecl
funcToDecl r = do
  let t = T.typeOf r
  let n = varName r
  env <- use envFuns
  case M.lookup r env of
    Nothing -> do
      sorts <- traverse typeToSort (T.domain t)
      sym <- mkStringSymbol n
      r' <- mkFuncDecl sym sorts =<< typeToSort (T.range t)
      fixedpointRegisterRelation r'
      envFuns %= M.insert r r'
      return r'
    Just r' -> return r'

formFromApp :: MonadZ3 z3 => String -> [AST] -> Sort -> z3 Form
formFromApp name args range
  | name == "true"  = return $ F.LBool True
  | name == "false" = return $ F.LBool False
  -- The 'app' is just a variable
  | null args = do
    typ <- sortToType range
    return $ F.V $ varForName name typ
  | name == "ite" || name == "if" = do
    c <- astToForm (head args)
    e1 <- astToForm (args !! 1)
    e2 <- astToForm (args !! 2)
    return $ F.appMany (F.If (T.typeOf e1)) [c, e1, e2]
  | name == "and"      = F.manyAnd  <$> traverse astToForm args
  | name == "or"       = F.manyOr   <$> traverse astToForm args
  | name == "+"        = F.manyIAdd <$> traverse astToForm args
  | name == "*"        = F.manyIMul <$> traverse astToForm args
  | name == "mod"      = liftMany (F.Mod T.Int)
  | name == "distinct" = liftMany (F.Distinct T.Int)
  | name == "div"      = lift2 (F.Div T.Int)
  | name == "iff"      = lift2 F.Iff
  | name == "=>"       = lift2 F.Impl
  | name == "<"        = lift2 (F.Lt T.Int)
  | name == "<="       = lift2 (F.Le T.Int)
  | name == ">"        = lift2 (F.Gt T.Int)
  | name == ">="       = lift2 (F.Ge T.Int)
  | name == "="        = F.mkEql T.Int <$> astToForm (head args) <*> astToForm (args !! 1)
  | name == "not"      = F.mkNot <$> astToForm (head args)
  | name == "-"        = if length args == 1
                         then F.app2 (F.Sub T.Int) (F.LInt 0) <$> astToForm (head args)
                         else lift2 (F.Sub T.Int)
  | name == "select"   = lift2 (F.Select T.Int T.Int)
  | name == "store"    = lift3 (F.Store T.Int T.Int)
  | otherwise = do
    -- Found a function that is as of yet unknown.
    liftIO $ putStrLn ("applying: " ++ name)
    args' <- traverse astToForm args
    domain <- traverse getType args
    range' <- sortToType range
    let f = varForName name (T.curryType domain range')
    return $ F.appMany (F.V f) args'
  where lift2 f = F.app2 f <$> astToForm (head args) <*> astToForm (args !! 1)
        lift3 f = F.app3 f <$> astToForm (head args)
                           <*> astToForm (args !! 1)
                           <*> astToForm (args !! 2)
        liftMany f = F.appMany f <$> traverse astToForm args

-- | Convert a Z3 model to the AST-based formula model.
modelToModel :: (MonadState Env z3, MonadZ3 z3) => Model -> z3 M.Model
modelToModel m = M.Model <$> (traverse superSimplify =<< M.union <$> functions <*> constants)
  where
    functions = do
      fds <- modelGetFuncDecls m
      fds' <- traverse declToFunc fds
      fi <- catMaybes <$> traverse (modelGetFuncInterp m) fds
      fe <- traverse (astToForm <=< funcInterpGetElse) fi
      return $ M.fromList $ zip fds' fe

    constants = do
      fds <- modelGetConstDecls m
      vs <- traverse declToFunc fds
      fi <- catMaybes <$> traverse (modelGetConstInterp m) fds
      fe <- traverse astToForm fi
      return $ M.fromList $ zip vs fe

    declToFunc fd = do
      name <- declName fd
      domain <- traverse sortToType =<< getDomain fd
      range  <- sortToType =<< getRange fd
      return $ varForName name (T.curryType domain range)

-- | Convert the Z3 internal representation of a formula to the AST representation.
astToForm :: MonadZ3 z3 => AST -> z3 Form
astToForm arg = do
  k <- getAstKind arg
  case k of
    Z3_NUMERAL_AST ->
      do t <- getType arg
         rep <- getNumeralString arg
         case t of
           T.Int  -> return $ F.LInt  $ read rep
           T.Real -> return $ F.LReal $ read rep
           _       -> error "unknown numeric type"

    Z3_APP_AST ->
      do app <- toApp arg
         decl <- getAppDecl app
         name <- declName decl
         args <- getAppArgs app
         range <- getRange decl
         formFromApp name args range

    Z3_VAR_AST -> F.V <$> (Bound <$> getIndexValue arg <*> getType arg)

    Z3_QUANTIFIER_AST -> do liftIO $ putStrLn "quantifier!"
                            undefined

    Z3_SORT_AST -> do liftIO $ putStrLn "sort!"
                      undefined

    Z3_FUNC_DECL_AST -> do liftIO $ putStrLn "func decl!"
                           undefined

    Z3_UNKNOWN_AST -> do liftIO $ putStrLn "unknown!"
                         undefined

varForName :: Name -> Type -> Var
varForName n t = case n of
  '!' : n' -> Bound (read n') t
  n' ->
    let ws = splitOn "/" n'
    in case readMaybe (last ws) of
      Nothing -> Free ws 0 t
      Just num -> Free (init ws) num t

typeToSort :: MonadZ3 z3 => Type -> z3 Sort
typeToSort = \case
  T.Unit       -> mkIntSort
  T.Bool       -> mkBoolSort
  T.Int        -> mkIntSort
  T.Real       -> mkRealSort
  T.Array t t' -> join $ mkArraySort <$> typeToSort t <*> typeToSort t'
  _ :=> _      -> undefined
  T.List _     -> undefined

sortToType :: MonadZ3 z3 => Sort -> z3 Type
sortToType s = do
  sk <- getSortKind s
  case sk of
    Z3_UNINTERPRETED_SORT  -> error "unsupported sort kind"
    Z3_BOOL_SORT           -> return T.Bool
    Z3_INT_SORT            -> return T.Int
    Z3_REAL_SORT           -> return T.Real
    Z3_BV_SORT             -> error "unsupported sort kind"
    Z3_ARRAY_SORT          -> do
      d <- sortToType =<< getArraySortDomain s
      r <- sortToType =<< getArraySortRange s
      return (T.Array d r)
    Z3_DATATYPE_SORT       -> error "unsupported sort kind"
    Z3_RELATION_SORT       -> error "unsupported sort kind"
    Z3_FINITE_DOMAIN_SORT  -> error "unsupported sort kind"
    Z3_FLOATING_POINT_SORT -> error "unsupported sort kind"
    Z3_ROUNDING_MODE_SORT  -> error "unsupported sort kind"
    Z3_UNKNOWN_SORT        -> error "unsupported sort kind"

getType :: MonadZ3 z3 => AST -> z3 Type
getType = getSort >=> sortToType

declName :: MonadZ3 z3 => FuncDecl -> z3 String
declName = getDeclName >=> getSymbolString

varDec :: MonadZ3 z3 => Var -> z3 FuncDecl
varDec v = do
  let t = T.typeOf v
  let n = varName v
  sym <- mkStringSymbol n
  mkFuncDecl sym [] =<< typeToSort t
