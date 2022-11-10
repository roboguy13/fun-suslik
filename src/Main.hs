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
import           Syntax.Simple.IsNullTranslation
import           Syntax.Simple.UnfoldConstructors
import           Syntax.Simple.UnfoldEmptyConstructors

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

      -- let (GenerateDef fnName argLayouts resultLayout:_) = directives
      -- print fnName
      -- print $
      -- -- putStrLn $
      --   -- ppr $
      --   -- defToSuSLik $
      --   -- unfoldConstructors layouts $
      --   -- defTranslateLayoutMatch layouts $
      --   -- unfoldEmptyConstructors layouts $
      --   runTypeCheck layouts adts fnDefs $
      --     instAndElaborate fnName argLayouts resultLayout $ lookupDef fnDefs fnName

      let doDirective :: Directive -> IO ()
          doDirective (GenerateDef fnName argLayouts resultLayout) = do
            putStrLn $
              ppr $
              defToSuSLik $
              unfoldConstructors layouts $
              translateIsNull layouts $
              defTranslateLayoutMatch layouts $
              -- unfoldEmptyConstructors layouts $
              runTypeCheck fnName layouts adts fnDefs $
                instAndElaborate fnName argLayouts resultLayout $ lookupDef fnDefs fnName
            putStrLn ""

      mapM_ doDirective directives

