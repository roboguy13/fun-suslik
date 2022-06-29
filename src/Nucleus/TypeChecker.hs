module Nucleus.TypeChecker
  where

import           Nucleus.Expr

import           Data.List
import           Data.Foldable
import           Data.Void

import           Control.Monad

import           Bound.Scope

typeCheckDef :: Def -> Bool
typeCheckDef (Def ty (name, params, body)) =
  case checkType mempty (mkLams params body) ty of
    Just _ -> True
    Nothing -> False

type TcEnv a = [(a, Type String)]

knownType :: Type String -> Type String -> Maybe ()
knownType ty ty' = guard (removeSrcLoc ty == removeSrcLoc ty')

endoArgs :: TcEnv String -> Type String -> [Expr String] -> Maybe (Type String)
endoArgs env ty tys = do
  mapM_ (\e -> checkType env e ty) tys
  Just ty

checkEndoArgs :: TcEnv String -> Type String -> Type String -> [Expr String] -> Maybe (Type String)
checkEndoArgs env ty ty' tys = do
  knownType ty ty'
  endoArgs env ty tys

checkType :: TcEnv String -> Expr String -> Type String -> Maybe (Type String)
checkType env e (Refinement {}) =
  error "checkType: Refinement types not yet implemented"
checkType env (Var srcLoc v) ty =
  case lookup v env of
    Nothing -> error $ "checkType: Cannot find " ++ show v ++ " in environment"
    Just ty' -> knownType ty ty' *> pure ty

checkType env (IntLit {}) ty = knownType (IntType NoSrcLoc) ty *> pure ty
checkType env (BoolLit {}) ty = knownType (BoolType NoSrcLoc) ty *> pure ty

checkType env (Add _ x y) ty = checkEndoArgs env (IntType NoSrcLoc) ty [x, y]
checkType env (Sub _ x y) ty = checkEndoArgs env (IntType NoSrcLoc) ty [x, y]
checkType env (Mul _ x y) ty = checkEndoArgs env (IntType NoSrcLoc) ty [x, y]

checkType env (f :@ x) ty = do
  xTy <- inferType env x
  checkType env f (Arr NoSrcLoc xTy ty) --(xTy :-> ty)

checkType env (Lam srcLoc v body) ty =
  case ty of
    a :-> b -> do
      checkType ((v, a):env) (instantiate1 (Var srcLoc v) body) b
    _ -> Nothing

checkType env (Ann ty e) ty' = do
  knownType (fmap absurd ty) ty'
  checkType env e (fmap absurd ty)

checkType env (Comb ConstF) ty =
  case ty of
    a :-> b :-> a' -> do
      knownType a a'
      pure ty
    _ -> Nothing

checkType env (Comb ComposeF) ty =
  case ty of
    (b :-> c) :-> (a :-> b') :-> (a' :-> c') -> do
      knownType a a'
      knownType b b'
      knownType c c'
      pure ty
    _ -> Nothing

checkType env (Comb Nil) ty =
  case ty of
    ListType _ -> Just ty
    _ -> Nothing

checkType env (Comb Cons) ty =
  case ty of
    a :-> ListType a' :-> ListType a'' -> do
      knownType a a'
      knownType a a''
      pure ty
    _ -> Nothing

checkType env (Comb Head) ty =
  case ty of
    ListType a :-> a' -> knownType a a' *> pure ty
    _ -> Nothing

checkType env (Comb Tail) ty =
  case ty of
    ListType a :-> ListType a' -> knownType a a' *> pure ty
    _ -> Nothing

checkType env (Comb Foldr) ty =
  case ty of
    (a :-> b :-> b') :-> b'' :-> ListType a' :-> b''' -> do
      knownType a a'
      knownType b b'
      knownType b b''
      knownType b b'''
      pure ty
    _ -> Nothing

checkType env (Comb Scanr) ty =
  case ty of
    (a :-> b :-> b') :-> b'' :-> ListType a' :-> ListType b''' -> do
      knownType a a'
      knownType b b'
      knownType b b''
      knownType b b'''
      pure ty
    _ -> Nothing

checkType env (Comb Map) ty =
  case ty of
    (a :-> b) :-> ListType a' :-> ListType b' -> do
      knownType a a'
      knownType b b'
      pure ty
    _ -> Nothing

checkType env (Comb Pair) ty =
  case ty of
    a :-> b :-> PairType a' b' -> do
      knownType a a'
      knownType b b'
      pure ty
    _ -> Nothing

checkType env (Comb Dup) ty =
  case ty of
    a :-> PairType a' a'' -> do
      knownType a a'
      knownType a a''
      pure ty
    _ -> Nothing

checkType env (Comb Fst) ty =
  case ty of
    PairType a b :-> a' -> knownType a a' *> pure ty
    _ -> Nothing

checkType env (Comb Snd) ty =
  case ty of
    PairType a b :-> b' -> knownType b b' *> pure ty
    _ -> Nothing

checkType env (Comb Swap) ty =
  case ty of
    PairType a b :-> PairType b' a' -> do
      knownType a a'
      knownType b b'
      pure ty
    _ -> Nothing

checkType env (Comb PairJoin) ty = error "checkType: PairJoin"

checkType env (Comb IfThenElse) ty =
  case ty of
    BoolType :-> a :-> a' :-> a'' -> do
      knownType a a'
      knownType a a''
      pure ty
    _ -> Nothing

checkType env (Comb Le) ty =
  case ty of
    IntType :-> IntType :-> BoolType -> pure ty
    BoolType :-> BoolType :-> BoolType -> pure ty
    _ -> Nothing

checkType env (Comb IntEq) ty =
  case ty of
    IntType :-> IntType :-> BoolType -> pure ty
    _ -> Nothing

checkType env (Comb c) ty = do
  ty' <- inferType env (Comb c)
  knownType ty ty'
  pure ty'

inferType :: TcEnv String -> Expr String -> Maybe (Type String)
inferType env (Var v) = lookup v env -- TODO: Should this produce a scope error?
inferType env (IntLit {}) = Just IntType
inferType env (BoolLit {}) = Just BoolType

inferType env (Add x y) = endoArgs env IntType [x, y]
inferType env (Sub x y) = endoArgs env IntType [x, y]
inferType env (Mul x y) = endoArgs env IntType [x, y]

inferType env (f :@ x) = do
  (a :-> b) <- inferType env f
  xTy <- inferType env x
  guard (a == xTy)
  Just b

inferType env (Lam {}) = Nothing

inferType env (Ann ty e) = checkType env e (fmap absurd ty)

inferType env (Comb Sum) = Just $ ListType IntType :-> IntType

inferType env (Comb Unit) = Just UnitType
inferType env (Comb IntEq) = Just $ IntType :-> IntType :-> BoolType

inferType env (Comb Not) = Just $ BoolType :-> BoolType
inferType env (Comb And) = Just $ BoolType :-> BoolType :-> BoolType
inferType env (Comb Or) = Just $ BoolType :-> BoolType :-> BoolType
inferType env (Comb {}) = Nothing

