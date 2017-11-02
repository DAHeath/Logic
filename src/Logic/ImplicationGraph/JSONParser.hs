{-# LANGUAGE OverloadedStrings #-}

module Logic.ImplicationGraph.JSONParser where

import           Control.Lens
import           Control.Monad

import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (mapMaybe)
import           Data.Text (Text, unpack)
import           Data.Aeson
import qualified Data.HashMap.Lazy as HML
import qualified Data.Optic.Graph as G
import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.Vector as V
import           Data.Text.Prettyprint.Doc

import           Logic.ImplicationGraph
import           Logic.Formula
import           Logic.Var
import           Logic.Type

-- | Read a bytestring containing JSON into a graph where the indices are names
-- for the program position.
parseGraphFromJSON :: BS.ByteString -> ImplGr String
parseGraphFromJSON str = maybe G.empty getParsedGraph (decode str)

newtype ParsedGraph = ParsedGraph { getParsedGraph :: ImplGr String }

data EdgeHolder = EdgeHolder
  { _ehStart :: Text
  , _ehEnd :: Text
  , _ehEdge :: Edge
  } deriving (Show, Data)

buildGraph :: [EdgeHolder] -> VertexMap -> ImplGr String
buildGraph edgeHolders verticesMap =
  let vertices = map (uncurry vertex) (M.toList verticesMap)
      edges = map (\(EdgeHolder v1 v2 edge) -> (unpack v1, unpack v2, edge)) edgeHolders
  in G.fromLists vertices edges
  where
    varsMap = varNameMap edgeHolders
    vertex idV varsList =
      ( unpack idV
      , InstanceV (mapMaybe (\v -> M.lookup (unpack v) varsMap) varsList) (LBool False))

instance FromJSON ParsedGraph where
  parseJSON (Object o) =
    ParsedGraph <$> (buildGraph <$> (parseJSON =<< o .: "edges")
                                <*> (parseJSON =<< o .: "vertices"))
  parseJSON _ = mzero

type VertexMap = Map Text [Text]

instance Pretty EdgeHolder where
  pretty (EdgeHolder t t' e) = pretty t <+> pretty t' <+> pretty e

instance FromJSON EdgeHolder where
  parseJSON (Object o) =
    do form <- parseJSON =<< o .: "formula"
       renamings <- o .: "rename"
       EdgeHolder <$> (o .: "start")
                  <*> (o .: "end")
                  <*> (Edge form <$> (mapVarRenamings form <$> parseJSON renamings))
  parseJSON _ = mzero

-- | A variable renaming is a substitution of one free variable name to another
-- while preserving type.
data VarRenaming = VarRenaming Text Text

instance FromJSON VarRenaming where
  parseJSON (Object o) =
    let (a, b) = head (HML.toList o) in
    VarRenaming a <$> parseJSON b
  parseJSON _ = mzero

-- | Construct a mapping of variable names to the variables themselves for every
-- variable in the data structure.
varNameMap :: Data a => a -> Map String Var
varNameMap f = M.fromList $ map (\(n, t) -> (n, Free n t)) (f ^.. vars . _Free)

-- | Given a list of variable renamings for a formula, construct a variable
-- substitution map.
mapVarRenamings :: Form -> [VarRenaming] -> Map Var Var
mapVarRenamings form =
  let formVars = varNameMap form
  in M.fromList . mapMaybe
      (\(VarRenaming a b) -> do
        va <- M.lookup (unpack a) formVars
        vb <- M.lookup (unpack b) formVars
        return (va, vb))

instance FromJSON Form where
  parseJSON (Object o) = case Prelude.head (HML.toList o) of
    (str, val) ->
      let withArg f = do
            [t] <- parseJSON val
            return (f t)
      in case str of
           "exprcons" -> do [lhs,rhs] <- parseJSON val
                            return $ lhs :@ rhs
           "var"      -> withArg V
           "if"       -> withArg If
           "not"      -> return Not
           "impl"     -> return Impl
           "iff"      -> return Iff
           "and"      -> return And
           "or"       -> return Or
           "add"      -> withArg Add
           "mul"      -> withArg Mul
           "sub"      -> withArg Sub
           "div"      -> withArg Div
           "mod"      -> withArg Mod
           "distinct" -> withArg Distinct
           "eql"      -> withArg Eql
           "lt"       -> withArg Lt
           "le"       -> withArg Le
           "gt"       -> withArg Gt
           "ge"       -> withArg Ge
           "lunit"    -> return LUnit
           "lbool"    -> withArg LBool
           "lint"     -> withArg LInt
           "lreal"    -> withArg LReal
           _          -> return (LBool False)
  parseJSON _ = mzero

instance FromJSON Var where
  parseJSON (Object o) =
    case Prelude.head (HML.toList o) of
      ("free", Data.Aeson.Array val) ->
        Free <$> parseJSON (V.head val) <*> parseJSON (V.last val)
      _ -> return $ Free "" Logic.Type.Unit
  parseJSON _ = mzero

instance FromJSON Type where
  parseJSON (Object o) =
    case Prelude.head (HML.toList o) of
      ("bool", _) -> return Logic.Type.Bool
      ("int", _)  -> return Logic.Type.Int
      ("real", _) -> return Logic.Type.Real
      _           -> return Logic.Type.Unit
  parseJSON _ = mzero
