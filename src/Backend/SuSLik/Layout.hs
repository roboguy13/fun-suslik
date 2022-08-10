module Backend.SuSLik.Layout
  where

import           Bound
import           Bound.Scope

import           Syntax.Expr

import           Backend.SuSLik.SSL
import           Backend.SuSLik.Monad

data Cond p a
  = NoCond (FsExpr p a)
  | Cond (FsExpr p a) -- | Condition
         (Scope () (Cond p) a)

instantiateLayout :: (Ord a, Eq b) => FsLayout p b a -> [Cond p a] -> SuSLik (IndPred b)
instantiateLayout layout alts = do
  let name = "_" <> fsLayoutName layout <> "_base"

  setIndPredName (fsLayoutName layout) name

  theIndAlts <- sequenceA $ zipWith3 instantiateLayoutAlt [0..] alts (fsLayoutAlts layout)

  pure MkIndPred
        { indPredName = name

        , indPredParams = -- XXX: For now, we make all parameters "loc"s
            map (::: LocS) $ fsLayoutTargetFVs (fsLayoutType layout)

        , indPredAlts = theIndAlts
        }

instantiateLayoutAlt :: (Eq a) => Int -> Cond p a -> FsAlt p a -> SuSLik (IndPredAlt b)
instantiateLayoutAlt ix cond defAlt = undefined

