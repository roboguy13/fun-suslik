{-# LANGUAGE LambdaCase #-}

module Main
  where

import           Syntax.Simple.Def
import           Syntax.Simple.Expr
import           Syntax.Simple.Parse
import           Syntax.Ppr

import           System.Environment

isBaseTypeName :: String -> Bool
isBaseTypeName "Int" = True
isBaseTypeName "Bool" = True
isBaseTypeName _ = False

main :: IO ()
main =
  getArgs >>= \case
    [] -> error "Expected a source filename"
    args@(_:_:_) -> error $ "Too many arguments. Expected 1, got " ++ show (length args)

    [fileName] -> do
      fileData <- readFile fileName
      let parsedFile = parse' parseFile fileData
          layouts = fileLayouts parsedFile
          fnDefs = fileFnDefs parsedFile

      case fileDirectives parsedFile of
        [InstantiateDef fnName [argLayout] resultLayout]
          | isBaseTypeName resultLayout ->
              mapM_ (putStrLn . ppr)
                $ genBaseDefPreds
                      layouts
                      (lookupLayout layouts argLayout)
                      (lookupDef fnDefs fnName)
          | otherwise ->
              mapM_ (putStrLn . ppr)
                $ genDefPreds
                      layouts
                      (lookupLayout layouts argLayout)
                      (lookupLayout layouts resultLayout)
                      (lookupDef fnDefs fnName)

        [InstantiateDef _ argLayouts _] ->
          error $
            unlines
              ["Given multiple layout arguments: " ++ show argLayouts
              ,"Only currently supports one layout argument and zero or more base type arguments."
              ]
