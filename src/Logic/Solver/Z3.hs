{-# LANGUAGE TemplateHaskell, ConstraintKinds #-}

module Logic.Solver.Z3 where

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Except

import           Data.List (partition)
import           Data.Maybe
import qualified Data.Map as M
import           Data.Map (Map)

import           Logic.Chc (Chc)
import qualified Logic.Chc as C
import           Logic.Formula (Form((:@)))
import qualified Logic.Formula as F
import           Logic.Var
import           Logic.Name
import           Logic.Type (Type((:=>)))
import qualified Logic.Type as T
import qualified Logic.Model as M

import           Z3.Monad hiding (local)

import Debug.Trace

data Env n = Env { _envVars :: Map (Var n) AST
                 , _envFuns :: Map (Var n) FuncDecl
                 } deriving (Show, Eq, Ord)
makeLenses ''Env

type SMT n m = (MonadState (Env n) m, MonadZ3 m)

-- | Invoke `duality` to solve the relational post fixed-point problem.
solveChc :: (Name n, MonadError (M.Model n) m, MonadIO m) => [Chc n] -> m (M.Model n)
solveChc hcs = do
  res <- runEnvZ3 sc
  case res of
    Left e -> throwError e
    Right m -> return m
  where
    sc = do
      let (queries, rules) = partition C.isQuery hcs
      let qids = map (const "x0/q") queries
      let qs = zipWith mkQuery queries qids
      let satForms = map F.toForm rules ++ qs
      let rids = map (\n -> "RULE" ++ show n) [0..length hcs-1]
      useDuality
      forms <- traverse formToAst satForms
      rids' <- traverse mkStringSymbol rids
      zipWithM_ fixedpointAddRule forms rids'

      let quers = [Free (fromJust $ "x0/q" ^? name) T.Bool]
      quers' <- traverse funcToDecl quers
      res <- fixedpointQueryRelations quers'
      case res of
        Unsat -> Right <$> (modelToModel =<< fixedpointGetModel)
        _     -> Left <$> (modelToModel =<< fixedpointGetRefutation)

    mkQuery q n =
      let theQuery = F.V $ Free (fromJust $ n ^? name) T.Bool in
      F.app2 F.Impl (F.mkNot $ F.toForm q) theQuery

    useDuality = do
      pars <- mkParams
      join $ paramsSetSymbol pars <$> mkStringSymbol "engine" <*> mkStringSymbol "duality"
      fixedpointSetParams pars

-- | Find a satisfying model of an input formula (if one exists).
satisfy :: (Name n, MonadIO m) => Form n -> m (Maybe (M.Model n))
satisfy f = runEnvZ3 $ do
  assert =<< formToAst f
  (_, m) <- solverCheckAndGetModel
  case m of
    Nothing -> return Nothing
    Just m' -> Just <$> modelToModel m'

-- | The the satisfiability of the input formula.
isSat :: (Name n, MonadIO m) => Form n -> m Bool
isSat f = do
  sol <- runEnvZ3 sc
  case sol of
    Sat -> return True
    _   -> return False
  where sc = (assert =<< formToAst f) >> check

-- | Test the validity of the input formula.
isValid :: (Name n, MonadIO m) => Form n -> m Bool
isValid f = runEnvZ3 $ do
  sol <- sc
  case sol of
    Unsat -> return True
    _     -> return False
  where sc = (assert =<< formToAst (F.mkNot f)) >> check

-- | Is `f -> g` a valid formula?
entails :: (Name n, MonadIO m) => Form n -> Form n -> m Bool
entails f g = isValid (F.app2 F.Impl f g)

simplify :: (Name n, MonadIO m) => Form n -> m (Form n)
simplify f = runEnvZ3 $ astToForm =<< Z3.Monad.simplify =<< formToAst f

superSimplify :: (Name n, MonadIO m) => Form n -> m (Form n)
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
        (f' : _) -> return f'
        _ -> return ast

-- | A monadic context for Z3 actions which caches the variables and functions
-- which have already been created. It also resolve DeBrujin indices which Z3
-- uses to represent variables.
newtype EnvZ3 n a = EnvZ3 { getEnvZ3 :: StateT (Env n) Z3 a }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadState (Env n)
           , MonadIO
           )

instance MonadZ3 (EnvZ3 n) where
  getSolver     = EnvZ3 $ lift getSolver
  getContext    = EnvZ3 $ lift getContext
  getFixedpoint = EnvZ3 $ lift getFixedpoint

runEnvZ3 :: (Name n, MonadIO m) => EnvZ3 n a -> m a
runEnvZ3 ac = liftIO $ evalZ3 (evalStateT (getEnvZ3 ac') emptyEnv)
  where
    ac' = push *> ac <* reset
    emptyEnv = Env M.empty M.empty

-- | Convert the ADT formula to a Z3 formula.
formToAst :: (Name n, SMT n m) => Form n -> m AST
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
    gatherApp :: Name n => Form n -> [Form n] -> (Form n, [Form n])
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
appToZ3 :: (Name n, SMT n m) => Form n -> [Form n] -> m AST
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

funcToDecl :: (Name n, MonadState (Env n) z3, MonadZ3 z3) => Var n -> z3 FuncDecl
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

formFromApp :: (Name n, MonadZ3 z3) => String -> [AST] -> Sort -> z3 (Form n)
formFromApp n args range
  | n == "true"  = return $ F.LBool True
  | n == "false" = return $ F.LBool False
  -- The 'app' is just a variable
  | null args = do
    typ <- sortToType range
    return $ F.V $ varForName n typ
  | n == "ite" || n == "if" = do
    c <- astToForm (head args)
    e1 <- astToForm (args !! 1)
    e2 <- astToForm (args !! 2)
    return $ F.appMany (F.If (T.typeOf e1)) [c, e1, e2]
  | n == "and"      = F.manyAnd  <$> traverse astToForm args
  | n == "or"       = F.manyOr   <$> traverse astToForm args
  | n == "+"        = F.manyIAdd <$> traverse astToForm args
  | n == "*"        = F.manyIMul <$> traverse astToForm args
  | n == "mod"      = liftMany (F.Mod T.Int)
  | n == "distinct" = liftMany (F.Distinct T.Int)
  | n == "div"      = lift2 (F.Div T.Int)
  | n == "iff"      = lift2 F.Iff
  | n == "=>"       = lift2 F.Impl
  | n == "<"        = lift2 (F.Lt T.Int)
  | n == "<="       = lift2 (F.Le T.Int)
  | n == ">"        = lift2 (F.Gt T.Int)
  | n == ">="       = lift2 (F.Ge T.Int)
  | n == "="        = F.mkEql T.Int <$> astToForm (head args) <*> astToForm (args !! 1)
  | n == "not"      = F.mkNot <$> astToForm (head args)
  | n == "-"        = if length args == 1
                         then F.app2 (F.Sub T.Int) (F.LInt 0) <$> astToForm (head args)
                         else lift2 (F.Sub T.Int)
  | n == "select"   = lift2 (F.Select T.Int T.Int)
  | n == "store"    = lift3 (F.Store T.Int T.Int)
  | otherwise = do
    -- Found a function that is as of yet unknown.
    liftIO $ putStrLn ("applying: " ++ n)
    args' <- traverse astToForm args
    domain <- traverse getType args
    range' <- sortToType range
    let f = varForName n (T.curryType domain range')
    return $ F.appMany (F.V f) args'
  where lift2 f = F.app2 f <$> astToForm (head args) <*> astToForm (args !! 1)
        lift3 f = F.app3 f <$> astToForm (head args)
                           <*> astToForm (args !! 1)
                           <*> astToForm (args !! 2)
        liftMany f = F.appMany f <$> traverse astToForm args

-- | Convert a Z3 model to the AST-based formula model.
modelToModel :: (Name n, MonadState (Env n) z3, MonadZ3 z3)
             => Model -> z3 (M.Model n)
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
      n <- declName fd
      domain <- traverse sortToType =<< getDomain fd
      range  <- sortToType =<< getRange fd
      if n == "@Fail!0"
      then return $ varForName "x0/Fail" (T.curryType domain range)
      else return $ varForName n (T.curryType domain range)

-- | Convert the Z3 internal representation of a formula to the AST representation.
astToForm :: (Name n, MonadZ3 z3) => AST -> z3 (Form n)
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
         n <- declName decl
         args <- getAppArgs app
         range <- getRange decl
         formFromApp n args range

    Z3_VAR_AST -> F.V <$> (Bound <$> (toInteger <$> getIndexValue arg) <*> getType arg)

    Z3_QUANTIFIER_AST -> do liftIO $ putStrLn "quantifier!"
                            undefined

    Z3_SORT_AST -> do liftIO $ putStrLn "sort!"
                      undefined

    Z3_FUNC_DECL_AST -> do liftIO $ putStrLn "func decl!"
                           undefined

    Z3_UNKNOWN_AST -> do liftIO $ putStrLn "unknown!"
                         undefined

varForName :: Name n => String -> Type -> Var n
varForName n t = case n of
  '!' : n' -> Bound (read n') t
  n' -> traceShow n' $
    Free (fromJust $ n' ^? name) t

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

varDec :: (Name n, MonadZ3 z3) => Var n -> z3 FuncDecl
varDec v = do
  let t = T.typeOf v
  let n = varName v
  sym <- mkStringSymbol n
  mkFuncDecl sym [] =<< typeToSort t
