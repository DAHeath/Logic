{-# LANGUAGE OverloadedStrings #-}

module Logic.ImplicationGraph.JSONParser where

import           Control.Monad

import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M
import qualified Data.List as L
import           Data.List.Split
import           Data.Text (Text, unpack)
import           Data.Aeson
import qualified Data.HashMap.Lazy as HML
import           Data.Optic.Directed.Graph (Graph)
import qualified Data.Optic.Directed.Graph as G
import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.Vector as V
import           Data.Text.Prettyprint.Doc

import           Logic.ImplicationGraph
import           Logic.Formula
import           Logic.Var
import           Logic.Type

-- | Read a bytestring containing JSON into a graph where the indices are names
-- for the program position.
parseGraphFromJSON :: BS.ByteString -> Maybe (Graph Line Edge Inst)
parseGraphFromJSON str = getParsedGraph <$> decode str

data Line = LineNo { qualifer :: [String], lineNo :: Integer }
  deriving (Data, Eq)

-- TODO: parse into int safely
textToLine :: Text -> Line
textToLine txt = LineNo path num
      where components = splitOn "/" $ unpack txt
            path = init components
            num = read $ last components

newtype ParsedGraph = ParsedGraph { getParsedGraph :: Graph Line Edge Inst }

-- | Maps an edge (defined by a start and an end index) to its label.
data EdgeHolder = EdgeHolder
  { _ehStart :: Line
  , _ehEnd :: Line
  , _ehEdge :: Edge
  } deriving (Show, Data)

-- | A map from each vertex to its neighbors. (Defines the graph topology.)
type VertexMap = Map Line [Var]

data JSONVertex
  = JInst [Var]
  | JQuery Form
  deriving (Show, Read, Eq, Ord, Data)

-- | Represents a variable renaming.
data VarRenaming = VarRenaming Var Var

renameMap :: [VarRenaming] -> Map Var Var
renameMap renames =
  M.fromList $ map tupelize renames
  where tupelize (VarRenaming a b) = (a, b)

buildGraph :: [EdgeHolder] -> Map Line JSONVertex -> Graph Line Edge Inst
buildGraph edgeHolders vertexMap =
  let
    vertices = map (\(iv, v) -> (iv, case v of
      JInst vs -> Inst (lineNo iv) vs (LBool False)
      JQuery q -> Inst (lineNo iv) [] q)) $ M.toList vertexMap
    edges = map (\(EdgeHolder v1 v2 e) -> (G.Pair v1 v2, e)) edgeHolders
  in
    G.fromLists vertices edges

instance Ord Line where
  compare (LineNo path num) (LineNo path' num') = case compare path path' of
    EQ -> compare num num'
    other -> other

instance Show Line where
  show (LineNo path num) = L.intercalate "/" $ path ++ [show num]

instance Pretty Line where
  pretty = pretty . show

instance Pretty EdgeHolder where
  pretty (EdgeHolder t t' e) = pretty t <+> pretty t' <+> pretty e

instance FromJSONKey Line where
  fromJSONKey = FromJSONKeyText textToLine

instance FromJSON Line where
  parseJSON (String txt) = return $ textToLine txt
  parseJSON _ = mzero

instance FromJSON ParsedGraph where
  parseJSON (Object o) = do
    edges <- o .: "edges" >>= parseJSON
    vertices <- o .: "vertices" >>= parseJSON
    return $ ParsedGraph $ buildGraph edges vertices
  parseJSON _ = mzero

instance FromJSON JSONVertex where
  parseJSON (Object o) = do
    kind <- o .: "type"
    live <- o .: "live" >>= parseJSON
    case kind of
      String t | t == "instance" ->
        return $ JInst live
      String t | t == "query" ->
        JQuery <$> (o .: "query" >>= parseJSON)
      _ -> mzero
  parseJSON _ = mzero

instance FromJSON EdgeHolder where
  parseJSON (Object o) = do
    start <- o .: "start"
    end <- o .: "end"
    formula <- o .: "formula" >>= parseJSON
    renamings <- o .: "rename" >>= parseJSON
    return $ EdgeHolder start end $ Edge formula $ renameMap renamings
  parseJSON _ = mzero

instance FromJSON VarRenaming where
  parseJSON (Data.Aeson.Array array) =
    case V.toList array of
      [v, v'] -> do
        original <- parseJSON v
        renamed <- parseJSON v'
        return $ VarRenaming original renamed
      _ -> mzero
  parseJSON _ = mzero

instance FromJSON Form where
  parseJSON (Object o) = case Prelude.head (HML.toList o) of
    (str, val) ->
      let withArg f = do
            [t] <- parseJSON val
            return (f t)
      in case str of
           "exprcons" -> (\[lhs, rhs] -> lhs :@ rhs) <$> parseJSON val
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
          return $ uncurry Free (unpackQID qid) kind
      _ -> mzero
  parseJSON _ = mzero

data QID = QID [String] Int

unpackQID :: QID -> ([String], Int)
unpackQID (QID path temporality) = (path, temporality)

instance FromJSON QID where
  parseJSON (Object o) =
    case HML.toList o of
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
