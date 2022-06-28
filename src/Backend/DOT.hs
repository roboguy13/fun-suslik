{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

module Backend.DOT where

import           Representation.Parts
import           EGraph.EGraph

import           Data.List.NonEmpty (NonEmpty (..))
import           Data.Foldable

import           Data.Map (Map)
import qualified Data.Map as Map

import qualified Data.Set as Set

import           Data.Data (Data, toConstr)

import           Data.Void

import           Control.Monad.State

data DOTConfig
  = DOTConfig
    { backgroundColor :: String
    , nodeColor :: String
    , nodeFontColor :: String
    , edgeColor :: String
    , graphMinSize :: Int
    }

defaultDOTConfig :: DOTConfig
defaultDOTConfig =
  DOTConfig
  { backgroundColor = "black"
  , nodeColor = "white"
  , nodeFontColor = "white"
  , edgeColor = "white"
  , graphMinSize = 25
  }

genConfig :: DOTConfig -> [String]
genConfig DOTConfig {..} =
  [ "graph [bgcolor=" <> backgroundColor <> " size=\"" <> show graphMinSize <> "!\"]"
  , "node [color=" <> nodeColor <> " fontcolor=" <> nodeFontColor <> "]"
  , "edge [color=" <> edgeColor <> "]"
  ]

data RenderState a =
  RenderState
  { renderStateNodeUniq :: Int
  , renderStateNodeMap :: Map a String
  }

data EGraphObj n = ENodeObj (ENode n) | EClassIdObj EClassId
  deriving (Eq, Ord)

newtype RenderM t a = RenderM { getRenderM :: State (RenderState t) a }
  deriving (Functor, Applicative, Monad, MonadState (RenderState t))

initialRenderState :: RenderState t
initialRenderState = RenderState 0 Map.empty

runRenderM :: RenderM t a -> a
runRenderM (RenderM m) = evalState m initialRenderState

insertFreshNode :: Ord t => t -> RenderM t String
insertFreshNode n = do
  nodeName <- freshNodeName
  modify $
    \x -> x { renderStateNodeMap = Map.insert n nodeName (renderStateNodeMap x) }
  pure nodeName

lookupNodeName :: Ord t => t -> RenderM t String
lookupNodeName n =
  fmap (Map.lookup n . renderStateNodeMap) get >>= \case
    Nothing -> error "lookupNodeName"
    Just r -> pure r

freshNodeName :: RenderM t String
freshNodeName = do
  currUniq <- renderStateNodeUniq <$> get
  modify $ \x -> x { renderStateNodeUniq = succ currUniq }
  return $ show currUniq

renderEGraphState :: forall n. (Show n, Ord n) => EGraphState n -> RenderM (EGraphObj n) String
renderEGraphState egraphState = do
  subgraphs <- mapM renderEClass (Map.elems (eclasses egraphState))
  enodeConnections <- mapM connectENode (Map.keys (hashcons egraphState))
  pure $
    unlines
      [ "strict digraph {"
      , indent subgraphs
      , indent enodeConnections
      , "}"
      ]
  where
    makeNewNode :: ENode n -> RenderM (EGraphObj n) String
    makeNewNode enode = do
      nodeName <- insertFreshNode (ENodeObj enode)
      pure $ genNode nodeName (enodeFun enode)

    makeNewClass :: EClassId -> RenderM (EGraphObj n) String
    makeNewClass eclassId =
      insertFreshNode (EClassIdObj eclassId)

      -- Used so that we have a DOT graph node to point to for the e-class
    eclassRepr :: EClassId -> RenderM (EGraphObj n) (ENode n)
    eclassRepr eclassId =
      case Map.lookup eclassId (eclasses egraphState) of
        Nothing -> error "renderEGraphState.eclassRepr"
        Just eclass ->
          pure $ Set.findMin (eclassNodes eclass)

    connectENode :: ENode n -> RenderM (EGraphObj n) String
    connectENode enode = do
      childClassReprs <- mapM eclassRepr (enodeChildren enode)

      unlines <$> mapM (enode `connectWithClasses`) childClassReprs

    renderEClass :: EClass n -> RenderM (EGraphObj n) String
    renderEClass eclass = do
      nodeDefs <- mapM makeNewNode (toList (eclassNodes eclass))
      className <- makeNewClass (eclassId eclass)
      pure $ genSubgraph className nodeDefs

    connectWithClasses :: ENode n -> ENode n -> RenderM (EGraphObj n) String
    connectWithClasses src tgt = do
      let Just srcClassId = Map.lookup src (hashcons egraphState)
          Just tgtClassId = Map.lookup tgt (hashcons egraphState)

      srcClassName <- lookupNodeName (EClassIdObj srcClassId)
      tgtClassName <- lookupNodeName (EClassIdObj tgtClassId)

      srcName <- lookupNodeName (ENodeObj src)
      tgtName <- lookupNodeName (ENodeObj tgt)

      pure $
        (srcName `connect` tgtName)
          ++ " [ltail=" ++ srcClassName ++ ", lhead=" ++ tgtClassName ++ "]"


genSubgraph :: String -> [String] -> String
genSubgraph name body =
  unlines
    [ "subgraph " ++ name ++ " {"
    , indent body
    , "}"
    ]


-- | A datatype generic renderer
genericRender :: forall a. (Show a, Data a, ToParts a) => a -> RenderM Void String
genericRender = renderParts . toParts

renderParts :: forall a. (Show a, Data a) => Parts a -> RenderM Void String
renderParts parts0 = do
  edges <- snd <$> go parts0

  pure $ unlines
    [ "strict digraph {"
    , indent edges
    , "}"
    ]
  where
    go :: Parts a -> RenderM Void (String, [String])
    go parts@(Leaf x) = do
      nodeName <- freshNodeName
      pure (nodeName, [genNode nodeName (rebuild parts)])
    go parts@(Parts cs f) = do
      nodeName <- freshNodeName

      rest <- toList <$> mapM go cs
      let connections = map (nodeName `connect`) $ map fst rest

      pure
        (nodeName,
          genNode nodeName (toConstr (rebuild parts))
            : (connections ++ concat (map snd rest)))

genNode :: (Show b) => String -> b -> String
genNode nodeName label =
  nodeName ++ " [label=" ++ show (show label) ++ "]"

connect :: String -> String -> String
connect a b = a ++ " -> " ++ b

indent :: [String] -> String
indent = unlines . map ("  " <>)

