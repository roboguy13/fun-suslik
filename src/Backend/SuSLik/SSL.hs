{-# LANGUAGE PatternSynonyms #-}

{-# OPTIONS_GHC -Wall #-}

module Backend.SuSLik.SSL
  where

import           Backend.Emit

import           Data.List

-- newtype Var = Var { getVarName :: String }

data SuSLikType = IntS | LocS | SetS | BoolS

data Spec a =
  MkSpec
  { specProcName :: String
  , specParams :: [Param a]
  , specPre :: Assertion a
  , specPost :: Assertion a
  }

data Param a = MkParam SuSLikType a

pattern (:::) :: a -> SuSLikType -> Param a
pattern x ::: ty = MkParam ty x

data IndPred a =
  MkIndPred
  { indPredName :: String
  , indPredParams :: [Param a]
  , indPredAlts :: [IndPredAlt a]
  }

data IndPredAlt a =
  MkIndPredAlt
  { indPredAltCond :: PFormula a
  , indPredAltAsn :: Assertion a
  }

data Assertion a =
  MkAssertion
  { assertionPure :: PFormula a
  , assertionSpatial :: SFormula a
  }

data SFormula a = MkSFormula [Heaplet a]

data PFormula a
  = PBool Bool
  | PInt Int
  | PGivenSet [PFormula a]

  | PVar a

  | PLt (PFormula a) (PFormula a)
  | PEq (PFormula a) (PFormula a)

  | PNot (PFormula a)
  | PAnd (PFormula a) (PFormula a)
  | POr (PFormula a) (PFormula a)

  | PIf (PFormula a) (PFormula a) (PFormula a)

  | PAdd (PFormula a) (PFormula a)
  | PSub (PFormula a) (PFormula a)
  | PMul (PFormula a) (PFormula a)

  | PUnion (PFormula a) (PFormula a)

conjunction :: [PFormula a] -> PFormula a
conjunction [] = PBool True
conjunction xs = foldr1 PAnd xs

data Heaplet a
  = PointsTo (a, Int) (HExpr a)
  | Block a Int
  | HeapletApp (HApp a)

pattern (:->) :: (a, Int) -> HExpr a -> Heaplet a
pattern x :-> y = PointsTo x y

data HApp a = MkHApp a [HExpr a]

-- | "Expressions" that can be pointed to
data HExpr a
  = HExprVar a
  | HExprApp (HApp a)

instance Emit a => Emit (IndPred a) where
  emit indPred =
    unlines'
      ["inductive " <> indPredName indPred <> "(" <> intercalate ", " (map emit (indPredParams indPred)) <> ") {"
      , unlines' $ map emit (indPredAlts indPred)
      ,"}"
      ]

instance Emit a => Emit (IndPredAlt a) where
  emit alt =
    "| " <> emit (indPredAltCond alt) <> " => " <> emit (indPredAltAsn alt)

instance Emit a => Emit (Spec a) where
  emit spec =
    unlines'
      ["void " <> specProcName spec <> withParens (intercalate ", " (map emit (specParams spec)))
      ,emit (specPre spec)
      ,emit (specPost spec)
      ,"{ ?? }"
      ]

instance Emit a => Emit (Param a) where
  emit (MkParam ty name) = unwords [emit ty, emit name]

instance Emit SuSLikType where
  emit IntS = "int"
  emit LocS = "loc"
  emit SetS = "set"
  emit BoolS = "bool"

instance Emit a => Emit (Assertion a) where
  emit (MkAssertion purePart spatialPart) =
    "{ " <> emit purePart <> " ; " <> emit spatialPart <> " }"


instance Emit a => Emit (SFormula a) where
  emit (MkSFormula []) = "emp"
  emit (MkSFormula xs) = intercalate " ** " (map emit xs)


instance Emit a => Emit (Heaplet a) where
  emit (PointsTo (x, 0) y) = emitBinOp ":->" x y
  emit (PointsTo (x, i) y) = emitBinOp ":->" (withParens (emit x <> "+" <> show i)) y
  emit (Block x sz) = "[" <> emit x <> ", " <> show sz <> "]"
  emit (HeapletApp h) = emit h

instance Emit a => Emit (HExpr a) where
  emit (HExprVar a) = emit a
  emit (HExprApp app) = emit app

instance Emit a => Emit (HApp a) where
  emit (MkHApp f args) = emit f <> withParens (intercalate ", " (map emit args))

instance Emit a => Emit (PFormula a) where
  emit (PBool True) = "true"
  emit (PBool False) = "false"

  emit (PInt i) = show i

  emit (PGivenSet xs) = "{" <> intercalate ", " (map emit xs) <> "}"

  emit (PVar v) = emit v

  emit (PLt x y) = emitBinOp "<" x y
  emit (PEq x y) = emitBinOp "==" x y

  emit (PNot x) = "not " <> withParens (emit x)
  emit (PAnd x y) = emitBinOp "&&" x y
  emit (POr x y) = emitBinOp "||" x y

  emit (PIf x y z) = withParens (emit x) <> " ? " <> withParens (emit y) <> " : " <> withParens (emit z)

  emit (PAdd x y) = emitBinOp "+" x y
  emit (PSub x y) = emitBinOp "-" x y
  emit (PMul x y) = emitBinOp "*" x y

  emit (PUnion x y) = emitBinOp "++" x y

-- filterExample :: Spec String
-- filterExample =
--   MkSpec
--     { specProcName = "filter"
--     , specParams = ["y" ::: LocS
--                    ,"ret" ::: LocS
--                    ,"v" ::: LocS
--                    ]
--     , specPre = MkAssertion (PBool True)
--                   (MkSFormula [("y", 0) :-> HExprVar "y0"
--                               ,HeapletApp (MkHApp "sll" [HExprVar "y0", HExprVar "s"])
--                               ,("ret", 0) :-> HExprVar "a"
--                               ,("v", 0) :-> HExprVar "vv"
--                               ])
--     , specPost = MkAssertion (PBool True)
--                   (MkSFormula [("y", 0) :-> HExprVar "y0"
--                               ,HeapletApp (MkHApp "base" [HExprVar "ret0", HExprVar "y0", HExprVar "s", HExprVar "vv"])
--                               ,("ret", 0) :-> HExprVar "ret0"
--                               ,("v", 0) :-> HExprVar "vv"
--                               ])
--     }
--
-- sllExample :: IndPred String
-- sllExample =
--   MkIndPred
--     { indPredName = "sll"
--     , indPredParams = ["x" ::: LocS
--                       ,"s" ::: SetS
--                       ]
--     , indPredAlts = [MkIndPredAlt
--                       { indPredAltCond = PEq (PVar "x") (PInt 0)
--                       , indPredAltAsn =
--                           MkAssertion (PEq (PVar "s") (PGivenSet []))
--                             $ MkSFormula [ ]
--                       }
--
--                     ,MkIndPredAlt
--                       { indPredAltCond = PNot (PEq (PVar "x") (PInt 0))
--                       , indPredAltAsn =
--                           MkAssertion (PEq (PVar "s") (PUnion (PGivenSet [PVar "v"]) (PVar "s1")))
--                             $ MkSFormula [Block "x" 2
--                                          ,("x", 0) :-> HExprVar "v"
--                                          ,("x", 1) :-> HExprVar "nxt"
--                                          ,HeapletApp (MkHApp "sll" [HExprVar "nxt", HExprVar "s1"])
--                                          ]
--                       }
--                     ]
--     }

