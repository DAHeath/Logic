{-# LANGUAGE OverloadedStrings #-}

module Logic.ImplicationGraph.JSONParser where

import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import           Data.Text (Text, unpack)
import           Logic.ImplicationGraph
import           Logic.Formula
import           Control.Monad
import           Data.Aeson
import qualified Data.HashMap.Lazy as HML
import           Logic.Var
import           Logic.Type
import qualified Data.Optic.Graph as G
import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.Vector as V
import           Data.Text.Prettyprint.Doc

parseGraphFromJSON :: BS.ByteString -> ImplGr String
parseGraphFromJSON jsonData = let maybeGraph = decode jsonData :: Maybe ParsedGraph
                                  (ParsedGraph graph) = Maybe.fromMaybe (ParsedGraph (G.fromLists [] [])) maybeGraph
                                    in graph


newtype ParsedGraph = ParsedGraph (ImplGr String)

buildGraph :: [EdgeHolder] -> VertexMap -> ImplGr String
buildGraph edgeHolders verticesMap = let varsMap = findVarsInEdges edgeHolders
                                         vertices = map (\ (idV, varsList) -> (unpack idV,
                                                              InstanceV (Maybe.mapMaybe (\ v -> Map.lookup (unpack v)
                                                                                              varsMap)
                                                                           varsList) (LBool False)))
                                                        (Map.toList verticesMap)
                                         edges = map (\ (EdgeHolder v1 v2 edge) -> (unpack v1, unpack v2, edge))
                                                     edgeHolders
                                             in G.fromLists vertices edges

instance FromJSON ParsedGraph where
  parseJSON (Object o) = do edges <- parseJSON <$> o .: "edges"
                            vertMap <- parseJSON <$> o .: "vertices"
                            ParsedGraph <$> (buildGraph <$> edges <*> vertMap)
  parseJSON _ = mzero


type VertexMap = Map Text [Text]

data EdgeHolder = EdgeHolder Text Text Edge
  deriving (Show)

instance Pretty EdgeHolder where
  pretty (EdgeHolder t t' e) = pretty t <+> pretty t' <+> pretty e

instance FromJSON EdgeHolder where
  parseJSON (Object o) = do form <- parseJSON <$> o .: "formula"
                            renamings <- o .: "rename"
                            EdgeHolder <$> (o .: "start")
                                       <*> (o .: "end")
                                       <*> (Edge <$> form <*> (mapVarRenamings <$> parseJSON renamings <*> form))
  parseJSON _ = mzero


data VarRenaming = VarRenaming Text Text

instance FromJSON VarRenaming where
  parseJSON (Object o) = let (a, b) = head (HML.toList o) in
                              do bParsed <- parseJSON b
                                 return $ VarRenaming a bParsed
  parseJSON _ = mzero



findVarsInEdges :: [EdgeHolder] -> Map String Var
findVarsInEdges = foldl (\ a (EdgeHolder _ _ (Edge form _)) -> Map.union a (findVars form)) (Map.fromList [])

-- findVar :: String -> Form -> Maybe Var
-- findVar name (lhs :@ rhs) = case findVar name lhs of
--                               Just var -> Just var
--                               Nothing  -> findVar name rhs
-- findVar name (V var) = case var of
--                           (Free currVarName _) -> if currVarName == name then Just var else Nothing
--                           _                -> Nothing
-- findVar _ _ = Nothing

findVars :: Form -> Map String Var
findVars (lhs :@ rhs) = Map.union (findVars lhs) (findVars rhs)
findVars (V var) = case var of
                      (Free name _) -> Map.fromList [(name, var)]
                      _             -> Map.fromList []
findVars _ = Map.fromList []


mapVarRenamings :: [VarRenaming] -> Form -> Map Var Var
mapVarRenamings renamings form = let formVars = findVars form in Map.fromList (Maybe.mapMaybe
      (\ (VarRenaming a b) -> let (va, vb) = (Map.lookup (unpack a) formVars, Map.lookup (unpack b) formVars) in
                                                case (va, vb) of
                                                  (Just ac, Just bc) -> Just (ac, bc)
                                                  _                  -> Nothing
                                                ) renamings)

instance FromJSON Form where
  parseJSON (Object o) = case Prelude.head (HML.toList o) of
                            ("exprcons", val) -> do [lhs,rhs] <- parseJSON val
                                                    return $ lhs :@ rhs
                            ("var", val)      -> do [v] <- parseJSON val
                                                    return $ V v
                            ("if", val)       -> do [t] <- parseJSON val
                                                    return $ If t
                            ("not", _)        -> return Not
                            ("impl", _)       -> return Impl
                            ("iff", _)        -> return Iff
                            ("and", _)        -> return And
                            ("or", _)         -> return Or
                            ("add", val)      -> do [t] <- parseJSON val
                                                    return $ Add t
                            ("mul", val)      -> do [t] <- parseJSON val
                                                    return $ Mul t
                            ("sub", val)      -> do [t] <- parseJSON val
                                                    return $ Sub t
                            ("div", val)      -> do [t] <- parseJSON val
                                                    return $ Div t
                            ("mod", val)      -> do [t] <- parseJSON val
                                                    return $ Mod t
                            ("distinct", val) -> do [t] <- parseJSON val
                                                    return $ Distinct t
                            ("eql", val)      -> do [t] <- parseJSON val
                                                    return $ Eql t
                            ("lt", val)       -> do [t] <- parseJSON val
                                                    return $ Lt t
                            ("le", val)       -> do [t] <- parseJSON val
                                                    return $ Le t
                            ("gt", val)       -> do [t] <- parseJSON val
                                                    return $ Gt t
                            ("ge", val)       -> do [t] <- parseJSON val
                                                    return $ Ge t
                            ("lunit", _)      -> return LUnit
                            ("lbool", val)    -> do [v] <- parseJSON val
                                                    return $ LBool v
                            ("lint", val)     -> do [v] <- parseJSON val
                                                    return $ LInt v
                            ("lreal", val)    -> do [v] <- parseJSON val
                                                    return $ LReal v
                            _                 -> return (LBool False)
  parseJSON _ = mzero

instance FromJSON Var where
  parseJSON (Object o) = case Prelude.head (HML.toList o) of
                            ("free", Data.Aeson.Array val) -> do name <- parseJSON (V.head val)
                                                                 tval <- parseJSON (V.last val)
                                                                 return $ Free name tval
                            _             -> return $ Free "" Logic.Type.Unit
  parseJSON _ = mzero

instance FromJSON Type where
  parseJSON (Object o) = case Prelude.head (HML.toList o) of
                            ("bool", _) -> return Logic.Type.Bool
                            ("int", _)  -> return Logic.Type.Int
                            ("real", _) -> return Logic.Type.Real
                            _           -> return Logic.Type.Unit
  parseJSON _ = mzero