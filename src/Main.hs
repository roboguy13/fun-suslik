{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LiberalTypeSynonyms #-}

module Main
  where

import           Syntax.Simple.Def
import           Syntax.Simple.Expr
import           Syntax.Simple.Parse
import           Syntax.Simple.TypeCheck
import           Syntax.Simple.Heaplet
import           Syntax.Simple.ToSuSLik
import           Syntax.Ppr

import           Syntax.Simple.TranslateLayoutMatch
import           Syntax.Simple.UnfoldConstructors

import           System.Environment

isBaseTypeName :: String -> Bool
isBaseTypeName "Int" = True
isBaseTypeName "Bool" = True
isBaseTypeName _ = False

main :: IO ()
main = do
  getArgs >>= \case
    [] -> error "Expected a source filename"
    args@(_:_:_) -> error $ "Too many arguments. Expected 1, got " ++ show (length args)

    [fileName] -> do
      fileData <- readFile fileName
      -- fileData <- readFile "examples/List.fsus"
      let parsed = parse' parseFile fileData
      let layouts = fileLayouts parsed
      let fnDefs = fileFnDefs parsed
      let adts = fileAdts parsed

      let directives = fileDirectives parsed

      let (GenerateDef fnName argLayouts resultLayout:_) = directives
      print fnName
      putStrLn $
        ppr $
        defToSuSLik $
        unfoldConstructors layouts $
        defTranslateLayoutMatch layouts $
        runTypeCheck layouts adts fnDefs $
          instAndElaborate fnName argLayouts resultLayout $ lookupDef fnDefs fnName

      -- print parsed
      -- print layouts


      -- let doDirective :: Directive -> IO ()
      --     doDirective (GenerateDef fnName [argLayout] resultLayout) = do
      --         if isBaseTypeName resultLayout
      --           then
      --             mapM_ (putStrLn . ppr)
      --               $ genBaseDefPreds
      --                     layouts
      --                     (lookupLayout layouts argLayout)
      --                     (lookupDef fnDefs fnName)
      --           else
      --             mapM_ (putStrLn . ppr)
      --               $ genDefPreds
      --                     layouts
      --                     (lookupLayout layouts argLayout)
      --                     (lookupLayout layouts resultLayout)
      --                     (lookupDef fnDefs fnName)
      --
      --         putStrLn ""
      --         putStrLn . ppr . genSig (lookupLayout layouts argLayout) $ lookupDef fnDefs fnName
      --
      --     doDirective (GenerateDef _ argLayouts _ ) =
      --       error $
      --         unlines
      --           ["Given multiple layout arguments: " ++ show argLayouts
      --           ,"Only currently supports one layout argument and zero or more base type arguments."
      --           ]
      --
      -- mapM_ (putStrLn . ppr . genLayoutPred) $ layouts
      -- mapM_ doDirective (fileDirectives parsed)
      --
