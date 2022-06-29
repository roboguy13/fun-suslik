module Nucleus.TypeChecker
  where

import           Nucleus.Expr

import           Data.List
import           Data.Foldable

import           Control.Monad

import           Bound.Scope

type TcEnv a = [(a, Type String)]

knownType :: Type String -> Type String -> Maybe (Type String)
knownType ty ty' = guard (ty == ty') *> Just ty'

endoArgs :: TcEnv a -> Type String -> Type String -> [ExprU uv a] -> Maybe (Type String)
endoArgs env ty ty' tys = do
  knownType ty ty'
  mapM_ (\e -> checkType env e ty) tys
  Just ty

checkType :: TcEnv a -> ExprU uv a -> Type String -> Maybe (Type String)
checkType env (Var v) ty =
  case lookup v env of
    Nothing -> error $ "checkType: Cannot find " ++ show v ++ " in environment"
    Just ty' -> knownType ty ty'

checkType env (IntLit {}) ty = knownType IntType ty
checkType env (BoolLit {}) ty = knownType BoolType ty

checkType env (Add x y) ty = endoArgs env IntType ty [x, y]
checkType env (Sub x y) ty = endoArgs env IntType ty [x, y]
checkType env (Mul x y) ty = endoArgs env IntType ty [x, y]

checkType env (f :@ x) ty = do
  xTy <- inferType env x
  checkType env f (xTy :-> ty)

checkType env (Lam body) ty =
  case ty of
    a :-> b -> do
      let v = head $ toList body
      checkType ((v, a):env) (unscope body) b
    _ -> Nothing

inferType :: TcEnv a -> ExprU uv a -> Maybe (Type String)
inferType = undefined

