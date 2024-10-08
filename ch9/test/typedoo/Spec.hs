module Spec where

import Expr
import TypeCheck
import TypeCheckerTest
  
import CommonParserUtil
import TokenInterface
import Lexer
import Parser

main :: IO ()
main = mapM_ doTest $ typechecker_tests'
  where
    TypeDeclTestSuite typechecker_tests' = typechecker_tests
    doTest (TDTC tcname expr_text maybeResult) =
      do putStr $ tcname ++ " : "

         expressionAst <-
           parsing False
              parserSpec ((), 1, 1, expr_text)
              (aLexer lexerSpec)
              (fromToken (endOfToken lexerSpec))

         let expression = expFrom expressionAst

         return undefined

        --  eitherTyOrErr <- typeCheck expression
         
        --  case eitherTyOrErr of
        --    Left errMsg ->
        --      case maybeResult of
        --        Just ty' -> putStrLn ("Expected " ++ show ty' ++ " but got " ++ errMsg ++ " in " ++ show expression)
        --        Nothing  -> putStrLn "Successfully type-unchecked." -- Is it the same error?
                 
        --    Right ty ->
        --      case maybeResult of
        --        Just ty' -> if equalType ty ty'
        --                    then putStrLn "Successfully typechecked."
        --                    else putStrLn ("Expected " ++ show ty' ++ " but got " ++ show ty ++ " in " ++ show expression)
                 
        --        Nothing  -> putStrLn "Should not be typechecked."
