--
-- Stage 4 here https://github.com/roboguy13/fun-suslik/blob/d5ccdc275ff13473f8e11af34deb8ce3523f6a9f/README.md
--

{-# LANGUAGE LiberalTypeSynonyms #-}

module Syntax.Simple.TranslateLayoutMatch
  (defTranslateLayoutMatch
  )
  where

import           Syntax.Simple.Heaplet
import           Syntax.Name


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
      MkGuardedExpr
        cond
        (MkExprWithAsn (foldMap applyPat pats) body)
      where

        applyPat :: Pattern' ParamTypeP -> Assertion SuSLikName
        applyPat (PatternVar {}) = Emp
        applyPat pat@(MkPattern (LayoutParam (MkParametrizedLayoutName params layoutName)) cName patParams) =
          let layout = lookupLayout layoutEnv (baseLayoutName layoutName)
              applied = removeHeapletApplies $ applyLayoutPat layout params (MkPattern () cName patParams)
          in
          if anyPatVarOccurs pat body || isEmp applied
            then removeHeapletApplies $ applyLayoutPat layout params (MkPattern () cName patParams)
            else HeapletApply layoutName (map VarS params) (map (Var ()) patParams) Emp
        applyPat pat@(MkPattern {}) = error $ "applyPat: Pattern match on non-layout: " ++ show pat


anyPatVarOccurs :: Pattern' a -> Expr FsName -> Bool
anyPatVarOccurs pat = any (`elem` getPatternVars pat)

