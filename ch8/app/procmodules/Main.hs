module Main where

import CommonParserUtil

import TokenInterface
import Lexer
import Terminal
import Parser
import Expr
import Interp
import TypeCheck

import Control.Monad (when)
import System.IO
import System.Environment (getArgs, withArgs)

main :: IO ()
main =
 do args <- getArgs
    _main args


_main [] = return ()
_main (fileName:args) = 
  case fileName of
    _ -> do _ <- doProcess True fileName
            _main args


doProcess verbose fileName = do
  text <- readFile fileName
  let debugFlag = False
        
  programAst <-
    parsing debugFlag
       parserSpec ((), 1, 1, text)
       (aLexer lexerSpec)
       (fromToken (endOfToken lexerSpec))

  let program = fromASTProgram programAst
  
  putStrLn (show program)

  eitherTyOrErr <- typeCheck program
  case eitherTyOrErr of
    Right ty ->
      do putStrLn (show ty)

         let val = value_of_program program
         putStrLn (show val)

    Left errMsg ->
      do putStrLn errMsg


