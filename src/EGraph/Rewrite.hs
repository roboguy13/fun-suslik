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

data Parts a
  = Parts (NonEmpty (Parts a)) (NonEmpty a -> a)
  | Leaf a

instance Eq a => Eq (Parts a) where
  x == y = rebuild x == rebuild y
  -- Parts ctrX csX _ == Parts ctrY csY _ = ctrX == ctrY && csX == csY
  -- Leaf x == Leaf y = x == y
  -- _ == _ = False

instance Ord a => Ord (Parts a) where
  compare x y = compare (rebuild x) (rebuild y)
  --   -- TODO: Does this work ok?
  -- compare (Parts ctrX csX _) (Parts ctrY csY _) = compare (show ctrX, csX) (show ctrY, csY)
  -- compare (Leaf x) (Leaf y) = compare x y
  -- compare (Leaf {}) (Parts {}) = LT
  -- compare (Parts {}) (Leaf {}) = GT

instance Show a => Show (Parts a) where
  show = show . rebuild

rebuild :: Parts a -> a
rebuild (Parts cs f) = f $ fmap rebuild cs
rebuild (Leaf x) = x

partsChildren :: Parts a -> [Parts a]
partsChildren (Parts xs _) = toList xs
partsChildren (Leaf _) = []

-- partsSplit :: Parts a -> ([Parts a], [Parts a] -> a)
-- partsSplit (Parts xs f) = (toList xs, f . xs)
-- partsSplit (Leaf x) = ([], const x)

overParts :: (Parts a -> Parts a) -> Parts a -> Parts a
overParts f (Parts xs g) = Parts (fmap f xs) g
overParts f (Leaf x) = f (Leaf x)

data Rewrite f uv a =
  Rewrite
  { rewriteLhs :: Parts (f uv a)
  , rewriteRhs :: Parts (f uv a)
  }

pattern lhs :=> rhs = Rewrite lhs rhs


-- | Gives the children as well as a function to reconstruct the node
-- given a new list of children
-- nodeDestruct :: Data n => n -> (Str n, Str n -> n)
-- nodeDestruct = uniplate

class ToParts n where
  toParts :: n -> Parts n

  nodeChildren :: n -> [n] -- This must eventually give back the empty list
  nodeChildren = map rebuild . partsChildren . toParts
  -- nodeChildren = toList . fst . nodeDestruct


-- toParts :: Data n => n -> Parts n
-- toParts n =
--   case nodeChildren n of
--     [] -> Leaf n
--     (x:xs) ->
--       Parts (toConstr n) (fmap toParts (x :| xs)) (snd (uniplate n) . listStr . toList)

fromParts :: Parts n -> n
fromParts (Parts cs f) = f (fmap fromParts cs)
fromParts (Leaf x) = x


-- instance Data a => TreeNode a where
--   nodeChildren x = gfoldl (\fs x -> x : map ($ x) fs) (const []) x

class Unify f where
  isUVar :: f uv a -> Maybe uv
  anyUVar :: f Void a -> f uv a
  anyUVar' :: Parts (f Void a) -> Parts (f uv a)

isUVar' :: Unify f => Parts (f uv a) -> Maybe uv
isUVar' (Leaf e) = isUVar e
isUVar' _ = Nothing

applyRewrite :: (Eq uv, Eq a, Eq (f uv a), Unify f) => Rewrite f uv a -> Parts (f Void a) -> Maybe (Parts (f uv a))
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

matchPartsList :: (Eq (f uv a), Eq uv, Unify f) => RewriteEnv f uv a -> [Parts (f uv a)] -> [Parts (f Void a)] -> Maybe (RewriteEnv f uv a)
matchPartsList env [] [] = Just env

matchPartsList env (Parts matchX fX : matchXS) (Parts e fE : es) = do
  env' <- matchPartsList env (toList matchX) (toList e)
  matchPartsList env' matchXS es

matchPartsList env (Leaf matchX : xs) (Leaf e : es) = do
  case isUVar matchX of
    Just uv -> void $ tryExtendEnv env uv (Leaf e)
    Nothing ->
      guard (matchX == anyUVar e)
  matchPartsList env xs es

matchPartsList _env _ _ = Nothing

  -- matchParts <$> (matchParts env (nodeChildren matchX) (nodeChildren e)) <*> pure matchXS <*> pure es

matchParts :: (Eq (f uv a), Eq uv, Unify f) => RewriteEnv f uv a -> Parts (f uv a) -> Parts (f Void a) -> Maybe (RewriteEnv f uv a)
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
tryExtendEnv :: (Eq uv) => RewriteEnv f uv a -> uv -> Parts (f Void a) -> Maybe (RewriteEnv f uv a)
tryExtendEnv env uv e =
  case lookup uv env of
    Nothing -> Just ((uv, e) : env)
    Just {} -> Nothing

