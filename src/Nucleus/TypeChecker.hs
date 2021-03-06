{-# LANGUAGE LambdaCase #-}

module Nucleus.TypeChecker
  where

import           Text.Megaparsec
import           Nucleus.Parser (offsetsToSourcePosList, SourcePosLine (..))

import           Nucleus.Expr

import           Data.List
import           Data.Void
import           Data.Either
import           Data.Foldable

import           Control.Monad
import           Control.Monad.Writer hiding (Sum)

import           Bound.Scope

data ErrorMsgPart = ErrorMsgPart String SrcLoc
  deriving (Show)

data TcError = TcError String [ErrorMsgPart]
  deriving (Show)

newtype TypeCheck a = TypeCheck { runTypeCheck :: WriterT [TcError] Maybe a }

getBasicMsg :: TcError -> String
getBasicMsg (TcError msg _) = msg

newtype TcErrorList = TcErrorList [TcError]

getFirstErrorLine :: TraversableStream s => PosState s -> TcError -> Maybe SourcePosLine
getFirstErrorLine _posState (TcError _ []) = Nothing
getFirstErrorLine posState (TcError str (ErrorMsgPart _ NoSrcLoc:xs)) = getFirstErrorLine posState (TcError str xs)
getFirstErrorLine posState (TcError _ (ErrorMsgPart _ (SrcLoc _ sp):_)) =
  case offsetsToSourcePosList posState [spanStart sp] of
    (r:_) -> Just r
    [] -> Nothing

typeCheckDef :: Def -> Either TcError (Type String)
typeCheckDef (Def ty (name, params, body)) =
  checkType mempty NoSrcLoc (mkLams params body) ty

type TcEnv a = [(a, Type String)]

knownType :: Type String -> Type String -> Either TcError ()
knownType ty ty' =
  if removeSrcLoc ty == removeSrcLoc ty'
    then pure ()
    else
      Left $
      TcError ("Cannot match expected type " ++ show (ppr ty) ++ " with actual type " ++ show (ppr ty'))
        [ ErrorMsgPart ("Expected " ++ show (ppr ty)) (getSrcLoc ty')
        ]

endoArgs :: TcEnv String -> SrcLoc -> Type String -> [Expr String] -> Either TcError (Type String)
endoArgs env parentTyLoc ty tys = do
  mapM_ (\e -> checkType env parentTyLoc e ty) tys
  pure ty

checkEndoArgs :: TcEnv String -> SrcLoc -> Type String -> Type String -> [Expr String] -> Either TcError (Type String)
checkEndoArgs env parentTyLoc ty ty' tys = do
  knownType ty ty'
  endoArgs env parentTyLoc ty tys

lookup' :: (Ppr a, Eq a) => String -> SrcLoc -> a -> [(a, b)] -> Either TcError b
lookup' origin srcLoc x env =
  case lookup x env of
    Nothing ->
      Left $
      TcError (origin ++ ": Cannot " ++ show (ppr x) ++ " in environment ")
        [ ErrorMsgPart "Cannot find this" srcLoc
        ]
    Just r -> pure r

expectedType :: TcEnv String -> String -> SrcLoc -> Expr String -> Either TcError a
expectedType env expected tyLoc e =
  Left $ TcError ("Expected " ++ expected ++ found)
    [ ErrorMsgPart ("Expected " ++ expected) (getSrcLoc e) --tyLoc
    ]
  where
    found =
      case inferType env tyLoc e of
        Left _ -> ""
        Right ty ->
          " but I inferred the type " ++ ppr ty

checkType :: TcEnv String -> SrcLoc -> Expr String -> Type String -> Either TcError (Type String)
checkType env _ e (Refinement {}) =
  error "checkType: Refinement types not yet implemented"
checkType env _ e@(Var srcLoc v) ty = do
  ty' <- lookup' "checkType" srcLoc v env
  knownType ty ty' *> pure ty

checkType env _ (IntLit {}) ty = knownType (IntType NoSrcLoc) ty *> pure ty
checkType env _ (BoolLit {}) ty = knownType (BoolType NoSrcLoc) ty *> pure ty

checkType env parentTyLoc (Add _ x y) ty = checkEndoArgs env (parentTyLoc <> getSrcLoc ty) (IntType NoSrcLoc) ty [x, y]
checkType env parentTyLoc (Sub _ x y) ty = checkEndoArgs env (parentTyLoc <> getSrcLoc ty) (IntType NoSrcLoc) ty [x, y]
checkType env parentTyLoc (Mul _ x y) ty = checkEndoArgs env (parentTyLoc <> getSrcLoc ty) (IntType NoSrcLoc) ty [x, y]

checkType env parentTyLoc e@(f :@ x) ty = do
  xTy <- inferType env (getSrcLoc ty) x
  checkType env (parentTyLoc <> getSrcLoc ty) f (Arr (parentTyLoc <> getSrcLoc ty) xTy ty) --(xTy :-> ty)

checkType env parentTyLoc e@(Lam srcLoc v body) ty =
  case ty of
    a :-> b -> do
      checkType ((v, a):env) (parentTyLoc <> getSrcLoc ty) (instantiate1 (Var srcLoc v) body) b
    _ -> expectedType env "_ -> _" (getSrcLoc ty) e

checkType env parentTyLoc (Ann srcLoc ty e) ty' = do
  knownType (fmap absurd ty) ty'
  checkType env (parentTyLoc <> getSrcLoc ty') e (fmap absurd ty)

checkType env _ e@(Comb srcLoc ConstF) ty =
  case ty of
    a :-> b :-> a' -> do
      knownType a a'
      pure ty
    _ -> expectedType env "_ -> _ -> _" (getSrcLoc ty) e

checkType env _ e@(Comb srcLoc ComposeF) ty =
  case ty of
    (b :-> c) :-> (a :-> b') :-> (a' :-> c') -> do
      knownType a a'
      knownType b b'
      knownType c c'
      pure ty
    _ -> expectedType env "(_ -> _) -> (_ -> _) -> (_ -> _)" (getSrcLoc ty) e

checkType env _ e@(Comb srcLoc Nil) ty =
  case ty of
    ListType _ _ -> pure ty
    _ -> expectedType env "List _" (getSrcLoc ty) e

checkType env _ e@(Comb srcLoc Cons) ty =
  case ty of
    a :-> ListType _ a' :-> ListType _ a'' -> do
      knownType a a'
      knownType a a''
      pure ty
    _ -> expectedType env "_ -> List _ -> List _" (getSrcLoc ty) e

checkType env _ e@(Comb srcLoc Head) ty =
  case ty of
    ListType _ a :-> a' -> knownType a a' *> pure ty
    _ -> expectedType env "List _ -> _" (getSrcLoc ty) e

checkType env _ e@(Comb srcLoc Tail) ty =
  case ty of
    ListType _ a :-> ListType _ a' -> knownType a a' *> pure ty
    _ -> expectedType env "List _ -> List _" (getSrcLoc ty) e

checkType env _ e@(Comb srcLoc Foldr) ty =
  case ty of
    (a :-> b :-> b') :-> b'' :-> ListType _ a' :-> b''' -> do
      knownType a a'
      knownType b b'
      knownType b b''
      knownType b b'''
      pure ty
    _ -> expectedType env "(_ -> _ -> _) -> List _ -> _" (getSrcLoc ty) e

checkType env _ e@(Comb srcLoc Scanr) ty =
  case ty of
    (a :-> b :-> b') :-> b'' :-> ListType _ a' :-> ListType _ b''' -> do
      knownType a a'
      knownType b b'
      knownType b b''
      knownType b b'''
      pure ty
    _ -> expectedType env "(_ -> _ -> _) -> List _ -> List _" (getSrcLoc ty) e

checkType env _ e@(Comb srcLoc Map) ty =
  case ty of
    (a :-> b) :-> ListType _ a' :-> ListType _ b' -> do
      knownType a a'
      knownType b b'
      pure ty
    _ -> expectedType env "(_ -> _) -> List _ -> List _" (getSrcLoc ty) e

checkType env _ e@(Comb srcLoc Pair) ty =
  case ty of
    a :-> b :-> PairType _ a' b' -> do
      knownType a a'
      knownType b b'
      pure ty
    _ -> expectedType env "_ -> _ -> Pair _ _" (getSrcLoc ty) e

checkType env _ e@(Comb srcLoc Dup) ty =
  case ty of
    a :-> PairType _ a' a'' -> do
      knownType a a'
      knownType a a''
      pure ty
    _ -> expectedType env "_ -> Pair _ _" (getSrcLoc ty) e

checkType env _ e@(Comb srcLoc Fst) ty =
  case ty of
    PairType _ a b :-> a' -> knownType a a' *> pure ty
    _ -> expectedType env "Pair _ _ -> _" (getSrcLoc ty) e

checkType env _ e@(Comb srcLoc Snd) ty =
  case ty of
    PairType _ a b :-> b' -> knownType b b' *> pure ty
    _ -> expectedType env "Pair _ _ -> _" (getSrcLoc ty) e

checkType env _ e@(Comb srcLoc Swap) ty =
  case ty of
    PairType _ a b :-> PairType _ b' a' -> do
      knownType a a'
      knownType b b'
      pure ty
    _ -> expectedType env "Pair _ _ -> Pair _ _" (getSrcLoc ty) e

checkType env _ e@(Comb srcLoc PairJoin) ty = error "checkType: PairJoin"

checkType env _ e@(Comb srcLoc IfThenElse) ty =
  case ty of
    BoolType _ :-> a :-> a' :-> a'' -> do
      knownType a a'
      knownType a a''
      pure ty
    _ -> expectedType env "Bool -> _ -> _ -> _" (getSrcLoc ty) e

checkType env _ e@(Comb srcLoc Le) ty =
  case ty of
    IntType _ :-> IntType _ :-> BoolType _ -> pure ty
    BoolType _ :-> BoolType _ :-> BoolType _ -> pure ty
    _ -> expectedType env "Int -> Int -> Int or Bool -> Bool -> Bool" (getSrcLoc ty) e

checkType env _ e@(Comb srcLoc IntEq) ty =
  case ty of
    IntType _ :-> IntType _ :-> BoolType _ -> pure ty
    _ -> expectedType env "Int -> Int -> Int" (getSrcLoc ty) e

checkType env _ e@(Comb srcLoc IdF) ty =
  case ty of
    x :-> x' -> do
      knownType x x'
      pure ty
    _ -> expectedType env "_ -> _" (getSrcLoc ty) e

checkType env _ e@(Comb srcLoc c) ty = do
  ty' <- inferType env (getSrcLoc ty) (Comb srcLoc c)
  knownType ty ty'
  pure ty'

inferType :: TcEnv String -> SrcLoc -> Expr String -> Either TcError (Type String)
inferType env _ (Var srcLoc v) = lookup' "inferType" srcLoc v env -- TODO: Should this produce a scope error?
inferType env _ (IntLit srcLoc _) = pure (IntType (setSrcLocKind InferredAt srcLoc))
inferType env _ (BoolLit srcLoc _) = pure (BoolType (setSrcLocKind InferredAt srcLoc))

inferType env tyLoc (Add srcLoc x y) = 
  endoArgs env tyLoc (IntType (setSrcLocKind InferredAt srcLoc)) [x, y]
inferType env tyLoc (Sub srcLoc x y) =
  endoArgs env tyLoc (IntType (setSrcLocKind InferredAt srcLoc)) [x, y]
inferType env tyLoc (Mul srcLoc x y) =
  endoArgs env tyLoc (IntType (setSrcLocKind InferredAt srcLoc)) [x, y]

inferType env srcLoc e@(f :@ x) =
  inferType env srcLoc f >>= \case
    a :-> b -> do
      xTy <- inferType env srcLoc x
      knownType a xTy
      pure b
    _ -> expectedType env "_ -> _" srcLoc e

inferType env _ e@(Lam {}) =
  Left $
  TcError "Cannot infer type of a lambda"
    [ ErrorMsgPart "Cannot infer type" (getSrcLoc e) ]

inferType env tyLoc (Ann srcLoc ty e) = checkType env tyLoc e (fmap absurd ty)

inferType env _ (Comb srcLoc0 Sum) =
  let srcLoc = setSrcLocKind InferredAt srcLoc0
  in
  pure $ Arr srcLoc (ListType srcLoc (IntType srcLoc)) (IntType srcLoc)

inferType env _ (Comb srcLoc Unit) = pure (UnitType (setSrcLocKind InferredAt srcLoc))
inferType env _ (Comb srcLoc0 IntEq) =
  let srcLoc = setSrcLocKind InferredAt srcLoc0
  in
  pure $ Arr srcLoc (IntType srcLoc) (Arr srcLoc (IntType srcLoc) (BoolType srcLoc))

inferType env _ (Comb srcLoc0 Not) =
  let srcLoc = setSrcLocKind InferredAt srcLoc0
  in
  pure $ Arr srcLoc (BoolType srcLoc) (BoolType srcLoc)
inferType env _ (Comb srcLoc0 And) =
  let srcLoc = setSrcLocKind InferredAt srcLoc0
  in
  pure $ Arr srcLoc (BoolType srcLoc) (Arr srcLoc (BoolType srcLoc) (BoolType srcLoc))
inferType env _ (Comb srcLoc0 Or) =
  let srcLoc = setSrcLocKind InferredAt srcLoc0
  in
  pure $ Arr srcLoc (BoolType srcLoc) (Arr srcLoc (BoolType srcLoc) (BoolType srcLoc))
inferType env _ e@(Comb {}) =
  Left $
  TcError ("Cannot infer type of combinator " ++ ppr e)
    [ ErrorMsgPart "Cannot infer type" (getSrcLoc e)
    ]

