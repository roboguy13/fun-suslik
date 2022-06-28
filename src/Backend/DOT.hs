{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Backend.DOT where

import           Representation.Parts

import           Data.List.NonEmpty (NonEmpty (..))
import           Data.Foldable

import           Data.Map (Map)
import qualified Data.Map as Map

import           Data.Data (Data, toConstr)

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

data RenderState =
  RenderState
  { renderStateNodeUniq :: Int
  }

newtype RenderM a = RenderM { getRenderM :: State RenderState a }
  deriving (Functor, Applicative, Monad, MonadState RenderState)

initialRenderState :: RenderState
initialRenderState = RenderState 0

runRenderM :: RenderM a -> a
runRenderM (RenderM m) = evalState m initialRenderState

freshNodeName :: RenderM String
freshNodeName = do
  currUniq <- renderStateNodeUniq <$> get
  modify $ \x -> x { renderStateNodeUniq = succ currUniq }
  return $ show currUniq

renderParts :: forall a. (Show a, Data a) => Parts a -> RenderM String
renderParts parts0 = do
  edges <- snd <$> go parts0

  pure $ unlines
    [ "strict digraph {"
    , indent edges
    , "}"
    ]
  where
    go :: Parts a -> RenderM (String, [String])
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

