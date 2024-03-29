--
-- Stage 4 here https://github.com/roboguy13/fun-suslik/blob/d5ccdc275ff13473f8e11af34deb8ce3523f6a9f/README.md
--

{-# LANGUAGE LiberalTypeSynonyms #-}

{-# OPTIONS_GHC -Wincomplete-patterns #-}

module Syntax.Simple.TranslateLayoutMatch
  (defTranslateLayoutMatch
  )
  where

import           Syntax.Simple.Heaplet
import           Syntax.Name

import           Data.Void

import Debug.Trace

defTranslateLayoutMatch :: [Layout] -> ElaboratedDef -> DefWithAsn
defTranslateLayoutMatch layoutEnv def =
  def
  { defBranches = map branchTranslate (defBranches def)
  }
  where

    branchTranslate :: ElaboratedDefBranch -> DefBranchWithAsn
    branchTranslate branch =
      branch
      { defBranchGuardeds = map (guardedTranslate (defBranchPatterns branch)) (defBranchGuardeds branch)
      }

    guardedTranslate :: [Pattern' ParamTypeP] -> Elaborated GuardedExpr -> GuardedExprWithAsn
    guardedTranslate pats (MkGuardedExpr cond body) =
      let asn = foldMap applyPat pats
      in
      MkGuardedExpr
        cond
        (MkExprWithAsn asn (updateAddrExprs asn body))
      where

        applyPat :: Pattern' ParamTypeP -> Assertion SuSLikName
        applyPat (PatternVar (LayoutParam p@(MkParametrizedLayoutName params0 layoutName)) v) =
          let params = map getLocBase params0
          in
          Emp --HeapletApply layoutName (map VarS params) [Var () v] Emp
        applyPat (PatternVar {}) = Emp
        applyPat pat@(MkPattern (LayoutParam (MkParametrizedLayoutName params0 layoutName)) cName patParams) =
          let params = map getLocBase params0
              layout = lookupLayout layoutEnv (baseLayoutName layoutName)
              applied = removeHeapletApplies layoutName $ applyLayoutPat layout params (MkPattern () cName patParams)
          in
          if anyPatVarOccurs pat body || isEmp applied
          then removeHeapletApplies layoutName $ applyLayoutPat layout params (MkPattern () cName patParams)
          else HeapletApply layoutName (map VarS params) (map (Var ()) patParams) Emp

        applyPat pat@(MkPattern {}) = error $ "applyPat: Pattern match on non-layout: " ++ show pat


anyPatVarOccurs :: Pattern' a -> Expr FsName -> Bool
anyPatVarOccurs pat = any (`elem` getPatternVars pat)

updateAddrExprs :: Assertion FsName -> ElaboratedExpr FsName -> ElaboratedExpr FsName
updateAddrExprs asn = go
  where
    go e0@(Var {}) = e0
    go e0@(IntLit {}) = e0
    go e0@(BoolLit {}) = e0
    go (And x y) = And (go x) (go y)
    go (Or x y) = Or (go x) (go y)
    go (Not x) = Not (go x)
    go (Add x y) = Add (go x) (go y)
    go (Sub x y) = Sub (go x) (go y)
    go (Mul x y) = Mul (go x) (go y)
    go (Equal x y) = Equal (go x) (go y)
    go (Le x y) = Le (go x) (go y)
    go (Lt x y) = Lt (go x) (go y)
    go (Apply f outTy inTys args) =
      Apply f outTy inTys $ map go args
    go (ConstrApply ty cName args) =
      ConstrApply ty cName $ map go args
    go (Lower ty _) = absurd ty
    go (Instantiate _ x _ _) = absurd x
    go (Deref ty x) = Deref ty (go x)
    go (Addr (PtrParam _ ty) (Var vTy v)) =
      Addr (PtrParam (Just (lookupAddr asn v)) ty) (Var vTy v)
    go (LetIn ty v rhs body) =
      LetIn ty v (go rhs) (go body)
    go (IfThenElse ty c t f) =
      IfThenElse ty (go c) (go t) (go f)

lookupAddr :: (Show a, Eq a) => Assertion a -> a -> Loc a
lookupAddr asn rhs = go asn
  where
    go Emp = error $ "lookupAddr (Emp): Cannot find " ++ show rhs
    go (PointsTo _mode x (VarS v) rest)
      | v == rhs = x
    go (PointsTo _ _ _ rest) = go rest
    go (HeapletApply _ _ _ rest) = go rest
    go (TempLoc _ rest) = go rest
    go (Block _ _ rest) = go rest
    go (IsNull _) = error $ "lookupAddr (IsNull): Cannot find " ++ show rhs
    go (Copy _ _ _) = error $ "lookupAddr (Copy): Cannot find " ++ show rhs
    go (AssertEqual _ _ rest) = go rest

