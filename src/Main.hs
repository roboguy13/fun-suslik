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
import System.IO
import System.Exit
import System.Process

import Control.Monad


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

data OutputKind = DirectOutput | IndirectOutput

setupOptions :: [String] -> (Options, [String])
setupOptions args =
  if "--no-ast-size" `elem` args
    then (MkOptions { optionsShowAstSize = False }, args \\ ["--no-ast-size"])
    else (MkOptions { optionsShowAstSize = True  }, args)

suslikOptions :: [String]
suslikOptions = ["--stdin", "true"
                -- ,"-o", "2"
                ,"-c", "2"
                ,"-b", "true"
                ,"-g", "true"
                ]

suslikCmd :: String
suslikCmd = "./suslik.sh"

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

          -- toHeapletsRec
          genLayoutPred :: Mode -> Layout -> String
          genLayoutPred mode layout =
            let branchHeaplets = map (getSuSLikAsnHeaplets . toHeapletsRec (Just mode) Nothing . snd) $ layoutBranches layout
                branchBlocks = map genBlocks' branchHeaplets

                pprAsn = pprLayoutBranch (layoutName layout) mode (layoutSuSLikParams layout)

                getBranchAsn :: [(FsName, Int)] -> (a, Assertion FsName) -> Assertion FsName
                getBranchAsn [] (_, asn) = asn
                getBranchAsn blocks (_, asn) = foldr (uncurry Block) asn blocks
            in
              unlines
                [ "predicate " <> genLayoutName (MkLayoutName (Just mode) (layoutName layout))
                               <> "(" <> intercalate ", " (map ("loc " ++) (layoutSuSLikParams layout)) <> ") {"
                , intercalate "\n" $ zipWith (\blocks -> pprAsn . getBranchAsn blocks) branchBlocks (layoutBranches layout)
                , "}"
                ]

          pprLayoutBranch :: String -> Mode -> [SuSLikName] -> Assertion FsName -> String
          pprLayoutBranch recName mode predParams asn =
            "| " ++ ppr (layoutCond predParams asn) ++ " => { " ++ ppr (toHeapletsRec (Just Input) Nothing (setAssertionModeRec recName mode asn)) ++ " }"

          getOutputTempName :: OutputKind -> String -> String
          getOutputTempName DirectOutput s = s
          getOutputTempName IndirectOutput s = s <> "0"

          genOutputHeaplet :: OutputKind -> String -> [Heaplet String]
          genOutputHeaplet DirectOutput _ = []
          genOutputHeaplet IndirectOutput name = 
            [PointsToS Unrestricted (Here name) (VarS (getOutputTempName IndirectOutput name))]

          genSpec :: OutputKind -> Directive -> Spec String
          genSpec outputKind (GenerateDef fnName argLayouts resultLayout) =
            let argNames = map (('x':) . show) $ zipWith const [1..] argLayouts
                resultName = "r"
                resultTempName = getOutputTempName outputKind resultName
                locName n = "loc " <> n
                freshVarName = "initialVal"

                -- precond param@LayoutParam{} n = Just $ genParamTypeName param <> "(" <> n <> ")"
                precond param@LayoutParam{} arg = Just $ HeapletApplyS (genParamTypeName param) [arg]
                precond _ _ = Nothing

                fnPredName = getPredName fnName (map genParamTypeName argLayouts) (genParamTypeName resultLayout)

                postcond = fnPredName <> "(" <> intercalate ", " argNames <> ", " <> resultTempName <> ")"
            in
            MkSpec
              { specFnName = fnName
              , specParams = map (LocTypeS,) (argNames ++ [resultName])
              , specPre = catMaybes (zipWith precond argLayouts (map VarS argNames)) ++ [PointsToS Unrestricted (Here resultName) (VarS freshVarName)]
              , specPost =
                    HeapletApplyS fnPredName (map VarS (argNames ++ [resultTempName]))
                    : genOutputHeaplet outputKind resultName
              }


      let fnPreds = map doDirective directives
          mkSpecs outputKind = map (genSpec outputKind) directives
          directSpecs = map (genSpec DirectOutput) directives
          mkOutString outputKind =
            ["// *** Layout predicates ***\n"
            ,unlines $ map (genLayoutPred Input) layouts
            ,"\n// *** Function predicates ***\n"
            ,unlines $ map ppr fnPreds
            ,"\n// *** Function specifications ***\n"
            ,unlines $ map ppr (mkSpecs outputKind)
            ]
          outString = mkOutString IndirectOutput
          directOutString = mkOutString DirectOutput

      -- (Just stdin_handle, Just stdout_handle, _stderr_handle, procHandle)
      --   <- createProcess (proc "./suslik/suslik" suslikOptions) { std_in = CreatePipe, std_out = CreatePipe }

      putStrLn (unlines outString)

      -- when (optionsShowAstSize options) $ do
      --   putStrLn $ "\n--- Source AST size: " ++ show (size parsed)
      --   putStrLn $ "\n--- SuSLik AST size: " ++ show (sum (map size layouts) + sum (map size fnPreds) + sum (map size specs))

      (exitCode, suslikOut, stderrOut) <- readCreateProcessWithExitCode (proc suslikCmd suslikOptions) (unlines outString)

      putStrLn suslikOut
      -- putStrLn stderrOut

      case exitCode of
        ExitSuccess -> putStrLn "Succeeded"
        ExitFailure e -> do
          putStrLn "######### Indirect output failed. Trying direct output..."
          putStrLn (unlines directOutString)
          (exitCode, suslikOut, stderrOut) <- readCreateProcessWithExitCode (proc suslikCmd suslikOptions) (unlines directOutString)
          putStrLn suslikOut
          putStrLn stderrOut
          exitWith exitCode

