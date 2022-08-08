{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}

module EGraph.Rewrite
  where

import           Data.Data

import           Data.Generics.Uniplate.Data
import           Data.Generics.UniplateStr (strList, listStr, Str)

import           Data.Foldable

import           Data.Void
import           Data.List
import           Data.List.NonEmpty (NonEmpty (..))

import           Control.Monad

import           Representation.Parts

data Rewrite f uv a =
  Rewrite
  { rewriteLhs :: Parts (f uv a)
  , rewriteRhs :: Parts (f uv a)
  }

pattern lhs :=> rhs = Rewrite lhs rhs

class Unify f where
  isUVar :: f uv a -> Maybe uv
  anyUVar :: f Void a -> f uv a
  anyUVar' :: Parts (f Void a) -> Parts (f uv a)

isUVar' :: Unify f => Parts (f uv a) -> Maybe uv
isUVar' (Leaf e) = isUVar e
isUVar' _ = Nothing

applyRewrite :: (Eq uv, Eq a, Eq (f uv a), Eq (f Void a), Unify f) => Rewrite f uv a -> Parts (f Void a) -> Maybe (Parts (f uv a))
applyRewrite (Rewrite lhs rhs) e = do
  env <- matchParts [] lhs e
  pure $ rewriteSubst env rhs

type RewriteEnv f uv a = [(uv, Parts (f Void a))]

rewriteSubst :: (Eq uv, Unify f) => RewriteEnv f uv a -> Parts (f uv a) -> Parts (f uv a)
rewriteSubst env e =
  case isUVar' e of
    Just uv ->
      case lookup uv env of
        Just s -> anyUVar' s
        Nothing -> error $ "rewriteSubst: Cannot find uvar in environment"
    Nothing ->
      case e of
        Leaf {} -> e
        _ -> overParts (rewriteSubst env) e
      -- let (children, f) = nodeDestruct e
      -- in
      -- f $ fmap (rewriteSubst env) children

matchPartsList :: (Eq (f uv a), Eq (f Void a), Eq uv, Unify f) => RewriteEnv f uv a -> [Parts (f uv a)] -> [Parts (f Void a)] -> Maybe (RewriteEnv f uv a)
matchPartsList env [] [] = Just env

matchPartsList env (Parts matchX fX : matchXS) (Parts e fE : es) = do
  env' <- matchPartsList env (toList matchX) (toList e)
  matchPartsList env' matchXS es

matchPartsList env (Leaf matchX : xs) (Leaf e : es) = do
  env' <- case isUVar matchX of
    Just uv -> tryExtendEnv env uv (Leaf e)
    Nothing ->
      if matchX == anyUVar e
        then pure env
        else Nothing

  matchPartsList env' xs es

matchPartsList _env _ _ = Nothing

  -- matchParts <$> (matchParts env (nodeChildren matchX) (nodeChildren e)) <*> pure matchXS <*> pure es

matchParts :: (Eq (f uv a), Eq (f Void a), Eq uv, Unify f) => RewriteEnv f uv a -> Parts (f uv a) -> Parts (f Void a) -> Maybe (RewriteEnv f uv a)
matchParts env x y = matchPartsList env [x] [y]

-- matchParts :: (Eq (f uv a), Eq uv, Unify f) => RewriteEnv f uv a -> Parts (f uv a) -> Parts (f Void a) -> Maybe (RewriteEnv f uv a)
-- matchParts env (Leaf matchX) (Leaf e) =
--   case isUVar matchX of
--     Just uv -> tryExtendEnv env uv (Leaf e)
--     Nothing -> do
--       guard (matchX == anyUVar e)
--       pure env
-- matchParts env (Parts matchXS matchsF) (Parts eXS eF) = do
--   -- env' <- matchParts env xChildren eChildren
--   sequenceA $ map (matchParts env) (zip matchXS eXS)
--
--   -- matchParts <$> (matchParts env (nodeChildren matchX) (nodeChildren e)) <*> pure matchXS <*> pure es
-- matchParts _env _ _ = Nothing


-- matchParts env (matchX:matchXS) (e:es) =
--   case (nodeChildren matchX, nodeChildren e) of
--
--     (xChildren, eChildren) -> do
--       env' <- matchParts env xChildren eChildren
--       matchParts env' matchXS es
--
--   -- matchParts <$> (matchParts env (nodeChildren matchX) (nodeChildren e)) <*> pure matchXS <*> pure es
-- matchParts _env _ _ = Nothing
--
tryExtendEnv :: (Eq uv, Eq (f Void a)) => RewriteEnv f uv a -> uv -> Parts (f Void a) -> Maybe (RewriteEnv f uv a)
tryExtendEnv env uv e =
  case lookup uv env of
    Nothing -> Just ((uv, e) : env)
    Just e' -> do
      guard (e' == e)
      Just env

