{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE TupleSections #-}

module Main where

import Syntax.Ppr
import Syntax.Simple.Def
import Syntax.Simple.Expr
import Syntax.Simple.Heaplet
import Syntax.Simple.Parse
import Syntax.Simple.Defunctionalize
import Syntax.Simple.ToSuSLik
import Syntax.Simple.TopLevelTranslation
import Syntax.Simple.TranslateLayoutMatch
import Syntax.Simple.TranslateLets
import Syntax.Simple.TypeCheck
import Syntax.Simple.UnfoldConstructors
import Syntax.Simple.UnfoldEmptyConstructors

import Syntax.Simple.SuSLik
import Syntax.Name

import System.Environment

import Data.List
import Data.Maybe

isBaseTypeName :: String -> Bool
isBaseTypeName "Int" = True
isBaseTypeName "Bool" = True
isBaseTypeName _ = False

data Options =
  MkOptions
  { optionsShowAstSize :: Bool
  }

setupOptions :: [String] -> (Options, [String])
setupOptions args =
  if "--no-ast-size" `elem` args
    then (MkOptions { optionsShowAstSize = False }, args \\ ["--no-ast-size"])
    else (MkOptions { optionsShowAstSize = True  }, args)

main :: IO ()
main = do
  (options, restArgs) <- fmap setupOptions getArgs
  case restArgs of
    [] -> error "Expected a source filename"
    args@(_ : _ : _) -> error $ "Too many arguments. Expected 1, got " ++ show (length args)
    [fileName] -> do
      fileData <- readFile fileName
      -- fileData <- readFile "examples/List.fsus"
      let parsed = parse' parseFile fileData
      let layouts = fileLayouts parsed
      let fnDefs0 = fileFnDefs parsed
      let adts = fileAdts parsed

      let (fnDefs1, generated) = fmap concat . unzip $ map (defunctionalize fnDefs0 layouts) fnDefs0
          generatedDirectives = map fst generated
          generatedDefs       = map snd generated
          fnDefs              = fnDefs1 ++ generatedDefs

      let directives0 = fileDirectives parsed
          directives = directives0 ++ generatedDirectives

      -- let (GenerateDef fnName argLayouts resultLayout:_) = directives
      -- print fnName
      -- -- print $
      -- putStrLn $
      --   ppr $
      --   defToSuSLik $
      --   unfoldConstructors layouts $
      --   defTranslateLayoutMatch layouts $
      --   unfoldEmptyConstructors layouts $
      --   runTypeCheck fnName layouts adts fnDefs $
      --     instAndElaborate fnName argLayouts resultLayout $ lookupDef fnDefs fnName

      let doDirective :: Directive -> InductivePred
          doDirective (GenerateDef fnName argLayouts resultLayout) =
            defToSuSLik $
              unfoldConstructors layouts $
                translateLets $
                  topLevelTranslate layouts $
                    defTranslateLayoutMatch layouts $
                      unfoldEmptyConstructors layouts $
                        runTypeCheck fnName layouts adts fnDefs $
                          instAndElaborate fnName argLayouts resultLayout $
                            lookupDef fnDefs fnName

          genLayoutPred :: Mode -> Layout -> IO ()
          genLayoutPred mode layout =
            putStrLn $
              unlines
                [ "predicate " <> genLayoutName (MkLayoutName (Just mode) (layoutName layout))
                               <> "(" <> intercalate ", " (map ("loc " ++) (layoutSuSLikParams layout)) <> ") {"
                , intercalate "\n" $ map (pprLayoutBranch (layoutName layout) mode (layoutSuSLikParams layout) . snd) (layoutBranches layout)
                , "}"
                ]

          pprLayoutBranch :: String -> Mode -> [SuSLikName] -> Assertion FsName -> String
          pprLayoutBranch recName mode predParams asn =
            "| " ++ ppr (layoutCond predParams asn) ++ " => { " ++ ppr (toHeapletsRec Nothing (setAssertionModeRec recName mode asn)) ++ " }"
            

          genSpec :: Directive -> Spec String
          genSpec (GenerateDef fnName argLayouts resultLayout) =
            let argNames = map (('x':) . show) $ zipWith const [1..] argLayouts
                resultName = "r"
                resultTempName = "r0"
                locName n = "loc " <> n

                -- precond param@LayoutParam{} n = Just $ genParamTypeName param <> "(" <> n <> ")"
                precond param@LayoutParam{} arg = Just $ HeapletApplyS (genParamTypeName param) [arg]
                precond _ _ = Nothing

                fnPredName = getPredName fnName (map genParamTypeName argLayouts) (genParamTypeName resultLayout)

                postcond = fnPredName <> "(" <> intercalate ", " argNames <> ", " <> resultTempName <> ")"
            in
            MkSpec
              { specFnName = fnName
              , specParams = map (LocType,) (argNames ++ [resultName])
              , specPre = catMaybes (zipWith precond argLayouts (map VarS argNames))
              , specPost =
                    [HeapletApplyS fnPredName (map VarS (argNames ++ [resultTempName]))
                    ,PointsToS Unrestricted (Here resultName) (VarS resultTempName)
                    ]
              }


      putStrLn "*** Layout predicates ***\n"
      mapM_ (genLayoutPred Input) layouts
      -- mapM_ (genLayoutPred Output) layouts

      let fnPreds = map doDirective directives

      putStrLn "\n*** Function predicates ***\n"
      mapM_ (putStrLn . ppr) fnPreds

      let specs = map genSpec directives

      putStrLn "\n*** Function specifications ***\n"
      mapM_ (putStrLn . ppr) specs

      putStrLn $ "\n--- Source AST size: " ++ show (size parsed)
      putStrLn $ "\n--- SuSLik AST size: " ++ show (sum (map size layouts) + sum (map size fnPreds) + sum (map size specs))

