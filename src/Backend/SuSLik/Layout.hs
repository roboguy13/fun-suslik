{-# OPTIONS_GHC -Wall #-}

module Backend.SuSLik.Layout
  where

import           Bound
import           Bound.Scope

import           Syntax.Expr

import           Backend.SuSLik.SSL
import           Backend.SuSLik.Monad

import           Data.List

data Cond p b a
  = NoCond (FsLayout p b a)
  | Cond (FsExpr p a) -- | Condition
         (Cond p b a)

instantiateLayout :: FsLayout p String String -> [Cond p String String] -> SuSLik String String (IndPred String)
instantiateLayout layout alts = do
  let name = "_" <> fsLayoutName layout <> "_base"

  setIndPredName (fsLayoutName layout) name

  -- let recParams = recursiveHeapParams name layout
  -- let nonrecParams = nonrecursiveHeapParams name layout 

  let paramType =
        if isRecursive layout
          then SetS
          else IntS -- XXX: For now, we just assume things are 'int's

  let ghosts = map toGhostName $ nonrecursiveHeapParams name layout

  theIndAlts <- sequenceA $ zipWith3 (instantiateLayoutAlt (PBool True) ghosts) [0..] alts (sortOn fst (fsLayoutAlts layout))

  pure MkIndPred
        { indPredName = name

        , indPredParams = -- XXX: For now, we make all parameters "loc"s
            map (::: LocS) (fsLayoutTargetFVs (fsLayoutType layout))
              ++ map (::: paramType) ghosts

        , indPredAlts = theIndAlts
        }

toGhostName :: String -> String
toGhostName str = str ++ "_ghost_"

newGhostName :: String -> String
newGhostName str = toGhostName str ++ "1"

toValueName :: String -> String
toValueName str = str ++ "_value_"

-- findValueName :: FsLayout p String String -> String -> String
-- findValueName layout locName =
--   case find go (getLayoutPointsTo layout) of
--     Nothing -> error $ "findValueName: Cannot find value param for " ++ locName
--     Just v -> v
--   where
--     go = undefined

setGhostUpdate :: String -> PFormula String
setGhostUpdate param =
  PEq (PVar (toGhostName param))
      (PUnion (PGivenSet [PVar (toValueName param)])
              (PVar (newGhostName param)))

instantiateLayoutAlt :: PFormula String -> [String] -> Int -> Cond p String String -> (ConName p String, LayoutBody p String String) -> SuSLik String String (IndPredAlt String)
instantiateLayoutAlt baseCond setParams ix (NoCond layout) (conName, LayoutBody layoutHeaplets) = do
  spatial <- mapM convertHeaplet layoutHeaplets

  pure MkIndPredAlt
    { indPredAltCond = baseCond
    , indPredAltAsn =
        MkAssertion
        { assertionPure = conjunction (map setGhostUpdate setParams)
        , assertionSpatial = MkSFormula spatial
        }
   }

instantiateLayoutAlt baseCond setParams ix (Cond c rest) (conName, LayoutBody layoutHeaplets) = do
  spatial <- mapM convertHeaplet layoutHeaplets

  pure MkIndPredAlt
    { indPredAltCond = toPFormula c
    , indPredAltAsn =
        MkAssertion
        { assertionPure = conjunction (map setGhostUpdate setParams)
        , assertionSpatial = MkSFormula spatial
        }
   }

-- | For now, only allows simple Boolean expressions (no lets, cases or
-- applications)
toPFormula :: FsExpr p String -> PFormula String
toPFormula (FsVar _ v) = PVar v
toPFormula (FsInt _ i) = PInt i
toPFormula (FsBool _ b) = PBool b
toPFormula (FsLam {}) = error "toPFormula: FsLam"
toPFormula (FsAdd _ x y) = PAdd (toPFormula x) (toPFormula y)
toPFormula (FsSub _ x y) = PSub (toPFormula x) (toPFormula y)
toPFormula (FsMul _ x y) = PMul (toPFormula x) (toPFormula y)
toPFormula (FsLt _ x y) = PLt (toPFormula x) (toPFormula y)
toPFormula (FsEq _ x y) = PEq (toPFormula x) (toPFormula y)
toPFormula (FsNot _ x) = PNot (toPFormula x)
toPFormula (FsAnd _ x y) = PAnd (toPFormula x) (toPFormula y)
toPFormula (FsOr _ x y) = POr (toPFormula x) (toPFormula y)
toPFormula _ = error "toPFormula"

locToName :: (String, Int) -> String
locToName (str, i) = str ++ "_" ++ show i

-- | Is this layout function recursive?
isRecursive :: FsLayout p b String -> Bool
isRecursive layout = any go (getLayoutApps layout)
  where
    go (f, _, _) = f == fsLayoutName layout

-- | Get the heap parameters that are used in recursive calls.
-- These will not be given a ghost representation
recursiveHeapParams :: (Eq a, Eq b) => a -> FsLayout p b a -> [b]
recursiveHeapParams recName layout =
  fsLayoutTargetFVs (fsLayoutType layout)
    `intersect` concatMap go (getLayoutApps layout)
  where
    go (f, heapParams, _)
      | f == recName = heapParams
      | otherwise = []

nonrecursiveHeapParams :: (Eq a, Eq b) => a -> FsLayout p b a -> [b]
nonrecursiveHeapParams recName layout =
  fsLayoutTargetFVs (fsLayoutType layout) \\ recursiveHeapParams recName layout

-- -- | Get the heap parameters that are used in recursive calls.
-- -- These will be used to create corresponding "set" parameters
-- recursiveHeapParams :: (Eq a, Eq b) => a -> FsLayout p b a -> [b]
-- recursiveHeapParams recName layout =
--   fsLayoutTargetFVs (fsLayoutType layout)
--     `intersect` concatMap go (getLayoutApps layout)
--   where
--     go (f, heapParams, _)
--       | f == recName = heapParams
--       | otherwise = []
--
-- -- | Get the heap parameters that are *not* used in recursive calls.
-- -- These will be used to create corresponding "int" or "bool" parameters.
-- nonrecursiveHeapParams :: (Eq a, Eq b) => a -> FsLayout p b a -> [b]
-- nonrecursiveHeapParams recName layout =
--   fsLayoutTargetFVs (fsLayoutType layout) \\ recursiveHeapParams recName layout

-- | NOTE: Ignores the "fun-SuSLik args" in applications
convertHeaplet :: LayoutHeaplet p String String -> SuSLik String String (Heaplet String)
convertHeaplet (LayoutPointsTo x y) = pure (x :-> HExprVar y)
convertHeaplet (LayoutBlock x sz) = pure (Block x sz)
convertHeaplet (LayoutHApply fn hArgs _fArgs) = do
  suslikName <- getIndPredName fn
  pure (HeapletApp (MkHApp suslikName (map HExprVar hArgs)))

