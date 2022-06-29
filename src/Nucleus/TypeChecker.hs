module Nucleus.TypeChecker
  where

import           Nucleus.Expr

import           Data.List
import           Data.Foldable
import           Data.Void

import           Control.Monad

import           Bound.Scope

data TcError = TcError SrcOffset String

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

checkType env (Ann srcLoc ty e) ty' = do
  knownType (fmap absurd ty) ty'
  checkType env e (fmap absurd ty)

checkType env (Comb srcLoc ConstF) ty =
  case ty of
    a :-> b :-> a' -> do
      knownType a a'
      pure ty
    _ -> Nothing

checkType env (Comb srcLoc ComposeF) ty =
  case ty of
    (b :-> c) :-> (a :-> b') :-> (a' :-> c') -> do
      knownType a a'
      knownType b b'
      knownType c c'
      pure ty
    _ -> Nothing

checkType env (Comb srcLoc Nil) ty =
  case ty of
    ListType _ _ -> Just ty
    _ -> Nothing

checkType env (Comb srcLoc Cons) ty =
  case ty of
    a :-> ListType _ a' :-> ListType _ a'' -> do
      knownType a a'
      knownType a a''
      pure ty
    _ -> Nothing

checkType env (Comb srcLoc Head) ty =
  case ty of
    ListType _ a :-> a' -> knownType a a' *> pure ty
    _ -> Nothing

checkType env (Comb srcLoc Tail) ty =
  case ty of
    ListType _ a :-> ListType _ a' -> knownType a a' *> pure ty
    _ -> Nothing

checkType env (Comb srcLoc Foldr) ty =
  case ty of
    (a :-> b :-> b') :-> b'' :-> ListType _ a' :-> b''' -> do
      knownType a a'
      knownType b b'
      knownType b b''
      knownType b b'''
      pure ty
    _ -> Nothing

checkType env (Comb srcLoc Scanr) ty =
  case ty of
    (a :-> b :-> b') :-> b'' :-> ListType _ a' :-> ListType _ b''' -> do
      knownType a a'
      knownType b b'
      knownType b b''
      knownType b b'''
      pure ty
    _ -> Nothing

checkType env (Comb srcLoc Map) ty =
  case ty of
    (a :-> b) :-> ListType _ a' :-> ListType _ b' -> do
      knownType a a'
      knownType b b'
      pure ty
    _ -> Nothing

checkType env (Comb srcLoc Pair) ty =
  case ty of
    a :-> b :-> PairType _ a' b' -> do
      knownType a a'
      knownType b b'
      pure ty
    _ -> Nothing

checkType env (Comb srcLoc Dup) ty =
  case ty of
    a :-> PairType _ a' a'' -> do
      knownType a a'
      knownType a a''
      pure ty
    _ -> Nothing

checkType env (Comb srcLoc Fst) ty =
  case ty of
    PairType _ a b :-> a' -> knownType a a' *> pure ty
    _ -> Nothing

checkType env (Comb srcLoc Snd) ty =
  case ty of
    PairType _ a b :-> b' -> knownType b b' *> pure ty
    _ -> Nothing

checkType env (Comb srcLoc Swap) ty =
  case ty of
    PairType _ a b :-> PairType _ b' a' -> do
      knownType a a'
      knownType b b'
      pure ty
    _ -> Nothing

checkType env (Comb srcLoc PairJoin) ty = error "checkType: PairJoin"

checkType env (Comb srcLoc IfThenElse) ty =
  case ty of
    BoolType _ :-> a :-> a' :-> a'' -> do
      knownType a a'
      knownType a a''
      pure ty
    _ -> Nothing

checkType env (Comb srcLoc Le) ty =
  case ty of
    IntType _ :-> IntType _ :-> BoolType _ -> pure ty
    BoolType _ :-> BoolType _ :-> BoolType _ -> pure ty
    _ -> Nothing

checkType env (Comb srcLoc IntEq) ty =
  case ty of
    IntType _ :-> IntType _ :-> BoolType _ -> pure ty
    _ -> Nothing

checkType env (Comb srcLoc c) ty = do
  ty' <- inferType env (Comb srcLoc c)
  knownType ty ty'
  pure ty'

inferType :: TcEnv String -> Expr String -> Maybe (Type String)
inferType env (Var srcLoc v) = lookup v env -- TODO: Should this produce a scope error?
inferType env (IntLit srcLoc _) = Just (IntType (setSrcLocKind InferredAt srcLoc))
inferType env (BoolLit srcLoc _) = Just (BoolType (setSrcLocKind InferredAt srcLoc))

inferType env (Add srcLoc x y) = 
  endoArgs env (IntType (setSrcLocKind InferredAt srcLoc)) [x, y]
inferType env (Sub srcLoc x y) =
  endoArgs env (IntType (setSrcLocKind InferredAt srcLoc)) [x, y]
inferType env (Mul srcLoc x y) =
  endoArgs env (IntType (setSrcLocKind InferredAt srcLoc)) [x, y]

inferType env (f :@ x) = do
  (a :-> b) <- inferType env f
  xTy <- inferType env x
  guard (a == xTy)
  Just b

inferType env (Lam {}) = Nothing

inferType env (Ann srcLoc ty e) = checkType env e (fmap absurd ty)

inferType env (Comb srcLoc Sum) =
  Just $ Arr (setSrcLocKind InferredAt srcLoc) (ListType NoSrcLoc (IntType NoSrcLoc)) (IntType NoSrcLoc)

inferType env (Comb srcLoc Unit) = Just (UnitType (setSrcLocKind InferredAt srcLoc))
inferType env (Comb srcLoc IntEq) =
  Just $ Arr (setSrcLocKind InferredAt srcLoc) (IntType NoSrcLoc) (IntType NoSrcLoc :-> BoolType NoSrcLoc)

inferType env (Comb srcLoc Not) =
  Just $ Arr (setSrcLocKind InferredAt srcLoc) (BoolType NoSrcLoc) (BoolType NoSrcLoc)
inferType env (Comb srcLoc And) =
  Just $ Arr (setSrcLocKind InferredAt srcLoc) (BoolType NoSrcLoc) (BoolType NoSrcLoc :-> BoolType NoSrcLoc)
inferType env (Comb srcLoc Or) =
  Just $ Arr (setSrcLocKind InferredAt srcLoc) (BoolType NoSrcLoc) (BoolType NoSrcLoc :-> BoolType NoSrcLoc)
inferType env (Comb {}) = Nothing

