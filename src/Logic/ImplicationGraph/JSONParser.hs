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
type Vertex = Text

-- | Maps an edge (defined by a start and an end index) to its label.
data EdgeHolder = EdgeHolder
  { _ehStart :: Vertex
  , _ehEnd :: Vertex
  , _ehEdge :: Edge
  } deriving (Show, Data)

-- | A map from each vertex to its neighbors. (Defines the graph topology.)
type VertexMap = Map Vertex [Vertex]

-- | Represents a variable renaming.
data VarRenaming = VarRenaming Var Var

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
      ("free", Data.Aeson.Array val) -> do
          qid <- parseJSON $ V.head val
          kind <- parseJSON $ V.last val
          return $ (uncurry Free) (unpackQID qid) kind
      _ -> mzero
  parseJSON _ = mzero

data QID = QID [String] Int
unpackQID (QID path temporality) = (path, temporality)

instance FromJSON QID where
  parseJSON (Object o) =
    case (HML.toList o) of
      ("qid", Data.Aeson.Array val) : _ ->
        let path = mapM parseJSON ((V.toList . V.init) val) in
        QID <$> path <*> parseJSON (V.last val)
      _ -> mzero
  parseJSON _ = mzero

instance FromJSON Type where
  parseJSON (Object o) =
    case Prelude.head (HML.toList o) of
      ("bool", _) -> return Logic.Type.Bool
      ("int", _)  -> return Logic.Type.Int
      ("real", _) -> return Logic.Type.Real
      _           -> return Logic.Type.Unit
  parseJSON _ = mzero
