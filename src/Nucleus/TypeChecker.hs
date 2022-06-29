{-# LANGUAGE LambdaCase #-}

module Nucleus.TypeChecker
  where

import           Nucleus.Expr

import           Data.List
import           Data.Foldable
import           Data.Void

import           Control.Monad

import           Bound.Scope

data ErrorMessage = ErrMsg String SrcLoc

data TcError = TcError [ErrorMessage]

instance Ppr ErrorMessage where
  pprP _ (ErrMsg text NoSrcLoc) = text
  pprP _ (ErrMsg text loc) = ppr loc ++ ": " ++ text

instance Ppr TcError where
  pprP _ (TcError msgs) = unwords (map ppr msgs)

err = Left . TcError
errNode node = ErrMsg (ppr node) (getSrcLoc node)
msg str = ErrMsg str NoSrcLoc

typeCheckDef :: Def -> Either TcError (Type String)
typeCheckDef (Def ty (name, params, body)) =
  checkType mempty (mkLams params body) ty

type TcEnv a = [(a, Type String)]

knownType :: Type String -> Type String -> Either TcError ()
knownType ty ty' =
  if removeSrcLoc ty == removeSrcLoc ty'
    then pure ()
    else
      err
        [ msg "Cannot match expected type"
        , errNode ty
        , msg "with actual type"
        , errNode ty'
        ]

endoArgs :: TcEnv String -> Type String -> [Expr String] -> Either TcError (Type String)
endoArgs env ty tys = do
  mapM_ (\e -> checkType env e ty) tys
  pure ty

checkEndoArgs :: TcEnv String -> Type String -> Type String -> [Expr String] -> Either TcError (Type String)
checkEndoArgs env ty ty' tys = do
  knownType ty ty'
  endoArgs env ty tys

lookup' :: (Ppr a, Eq a) => String -> SrcLoc -> a -> [(a, b)] -> Either TcError b
lookup' origin srcLoc x env =
  case lookup x env of
    Nothing ->
      err
        [ msg $ origin ++ ": Cannot find "
        , ErrMsg (ppr x) srcLoc
        , msg " in environment"
        ]
    Just r -> pure r

expectedType :: TcEnv String -> String -> Expr String -> Either TcError a
expectedType env expected e =
  err
    [ ErrMsg ("Expected " ++ expected ++ found) (getSrcLoc e)
    ]
  where
    found =
      case inferType env e of
        Left _ -> ""
        Right ty -> " but I inferred the type " ++ ppr ty

checkType :: TcEnv String -> Expr String -> Type String -> Either TcError (Type String)
checkType env e (Refinement {}) =
  error "checkType: Refinement types not yet implemented"
checkType env e@(Var srcLoc v) ty = do
  ty' <- lookup' "checkType" srcLoc v env
  knownType ty ty' *> pure ty

checkType env (IntLit {}) ty = knownType (IntType NoSrcLoc) ty *> pure ty
checkType env (BoolLit {}) ty = knownType (BoolType NoSrcLoc) ty *> pure ty

checkType env (Add _ x y) ty = checkEndoArgs env (IntType NoSrcLoc) ty [x, y]
checkType env (Sub _ x y) ty = checkEndoArgs env (IntType NoSrcLoc) ty [x, y]
checkType env (Mul _ x y) ty = checkEndoArgs env (IntType NoSrcLoc) ty [x, y]

checkType env (f :@ x) ty = do
  xTy <- inferType env x
  checkType env f (Arr NoSrcLoc xTy ty) --(xTy :-> ty)

checkType env e@(Lam srcLoc v body) ty =
  case ty of
    a :-> b -> do
      checkType ((v, a):env) (instantiate1 (Var srcLoc v) body) b
    _ -> expectedType env "_ -> _" e

checkType env (Ann srcLoc ty e) ty' = do
  knownType (fmap absurd ty) ty'
  checkType env e (fmap absurd ty)

checkType env e@(Comb srcLoc ConstF) ty =
  case ty of
    a :-> b :-> a' -> do
      knownType a a'
      pure ty
    _ -> expectedType env "_ -> _ -> _" e

checkType env e@(Comb srcLoc ComposeF) ty =
  case ty of
    (b :-> c) :-> (a :-> b') :-> (a' :-> c') -> do
      knownType a a'
      knownType b b'
      knownType c c'
      pure ty
    _ -> expectedType env "(_ -> _) -> (_ -> _) -> (_ -> _)" e

checkType env e@(Comb srcLoc Nil) ty =
  case ty of
    ListType _ _ -> pure ty
    _ -> expectedType env "List _" e

checkType env e@(Comb srcLoc Cons) ty =
  case ty of
    a :-> ListType _ a' :-> ListType _ a'' -> do
      knownType a a'
      knownType a a''
      pure ty
    _ -> expectedType env "_ -> List _ -> List _" e

checkType env e@(Comb srcLoc Head) ty =
  case ty of
    ListType _ a :-> a' -> knownType a a' *> pure ty
    _ -> expectedType env "List _ -> _" e

checkType env e@(Comb srcLoc Tail) ty =
  case ty of
    ListType _ a :-> ListType _ a' -> knownType a a' *> pure ty
    _ -> expectedType env "List _ -> List _" e

checkType env e@(Comb srcLoc Foldr) ty =
  case ty of
    (a :-> b :-> b') :-> b'' :-> ListType _ a' :-> b''' -> do
      knownType a a'
      knownType b b'
      knownType b b''
      knownType b b'''
      pure ty
    _ -> expectedType env "(_ -> _ -> _) -> List _ -> _" e

checkType env e@(Comb srcLoc Scanr) ty =
  case ty of
    (a :-> b :-> b') :-> b'' :-> ListType _ a' :-> ListType _ b''' -> do
      knownType a a'
      knownType b b'
      knownType b b''
      knownType b b'''
      pure ty
    _ -> expectedType env "(_ -> _ -> _) -> List _ -> List _" e

checkType env e@(Comb srcLoc Map) ty =
  case ty of
    (a :-> b) :-> ListType _ a' :-> ListType _ b' -> do
      knownType a a'
      knownType b b'
      pure ty
    _ -> expectedType env "(_ -> _) -> List _ -> List _" e

checkType env e@(Comb srcLoc Pair) ty =
  case ty of
    a :-> b :-> PairType _ a' b' -> do
      knownType a a'
      knownType b b'
      pure ty
    _ -> expectedType env "_ -> _ -> Pair _ _" e

checkType env e@(Comb srcLoc Dup) ty =
  case ty of
    a :-> PairType _ a' a'' -> do
      knownType a a'
      knownType a a''
      pure ty
    _ -> expectedType env "_ -> Pair _ _" e

checkType env e@(Comb srcLoc Fst) ty =
  case ty of
    PairType _ a b :-> a' -> knownType a a' *> pure ty
    _ -> expectedType env "Pair _ _ -> _" e

checkType env e@(Comb srcLoc Snd) ty =
  case ty of
    PairType _ a b :-> b' -> knownType b b' *> pure ty
    _ -> expectedType env "Pair _ _ -> _" e

checkType env e@(Comb srcLoc Swap) ty =
  case ty of
    PairType _ a b :-> PairType _ b' a' -> do
      knownType a a'
      knownType b b'
      pure ty
    _ -> expectedType env "Pair _ _ -> Pair _ _" e

checkType env e@(Comb srcLoc PairJoin) ty = error "checkType: PairJoin"

checkType env e@(Comb srcLoc IfThenElse) ty =
  case ty of
    BoolType _ :-> a :-> a' :-> a'' -> do
      knownType a a'
      knownType a a''
      pure ty
    _ -> expectedType env "Bool -> _ -> _ -> _" e

checkType env e@(Comb srcLoc Le) ty =
  case ty of
    IntType _ :-> IntType _ :-> BoolType _ -> pure ty
    BoolType _ :-> BoolType _ :-> BoolType _ -> pure ty
    _ -> expectedType env "Int -> Int -> Int or Bool -> Bool -> Bool" e

checkType env e@(Comb srcLoc IntEq) ty =
  case ty of
    IntType _ :-> IntType _ :-> BoolType _ -> pure ty
    _ -> expectedType env "Int -> Int -> Int" e

checkType env e@(Comb srcLoc c) ty = do
  ty' <- inferType env (Comb srcLoc c)
  knownType ty ty'
  pure ty'

inferType :: TcEnv String -> Expr String -> Either TcError (Type String)
inferType env (Var srcLoc v) = lookup' "inferType" srcLoc v env -- TODO: Should this produce a scope error?
inferType env (IntLit srcLoc _) = pure (IntType (setSrcLocKind InferredAt srcLoc))
inferType env (BoolLit srcLoc _) = pure (BoolType (setSrcLocKind InferredAt srcLoc))

inferType env (Add srcLoc x y) = 
  endoArgs env (IntType (setSrcLocKind InferredAt srcLoc)) [x, y]
inferType env (Sub srcLoc x y) =
  endoArgs env (IntType (setSrcLocKind InferredAt srcLoc)) [x, y]
inferType env (Mul srcLoc x y) =
  endoArgs env (IntType (setSrcLocKind InferredAt srcLoc)) [x, y]

inferType env e@(f :@ x) =
  inferType env f >>= \case
    a :-> b -> do
      xTy <- inferType env x
      knownType a xTy
      pure b
    _ -> expectedType env "_ -> _" e

inferType env e@(Lam {}) = err [ ErrMsg "Cannot infer type of a lambda" (getSrcLoc e) ]

inferType env (Ann srcLoc ty e) = checkType env e (fmap absurd ty)

inferType env (Comb srcLoc Sum) =
  pure $ Arr (setSrcLocKind InferredAt srcLoc) (ListType NoSrcLoc (IntType NoSrcLoc)) (IntType NoSrcLoc)

inferType env (Comb srcLoc Unit) = pure (UnitType (setSrcLocKind InferredAt srcLoc))
inferType env (Comb srcLoc IntEq) =
  pure $ Arr (setSrcLocKind InferredAt srcLoc) (IntType NoSrcLoc) (IntType NoSrcLoc :-> BoolType NoSrcLoc)

inferType env (Comb srcLoc Not) =
  pure $ Arr (setSrcLocKind InferredAt srcLoc) (BoolType NoSrcLoc) (BoolType NoSrcLoc)
inferType env (Comb srcLoc And) =
  pure $ Arr (setSrcLocKind InferredAt srcLoc) (BoolType NoSrcLoc) (BoolType NoSrcLoc :-> BoolType NoSrcLoc)
inferType env (Comb srcLoc Or) =
  pure $ Arr (setSrcLocKind InferredAt srcLoc) (BoolType NoSrcLoc) (BoolType NoSrcLoc :-> BoolType NoSrcLoc)
inferType env e@(Comb {}) = err [ ErrMsg ("Cannot infer type of combinator " ++ ppr e) (getSrcLoc e) ]

