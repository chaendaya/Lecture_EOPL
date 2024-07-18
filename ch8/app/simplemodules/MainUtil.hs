module MainUtil where

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

parser text = do
  parsing False                            -- parser converting a text-based program
     parserSpec ((), 1, 1, text)           -- into a program in abstract syntax tree (Expr)
     (aLexer lexerSpec)
     (fromToken (endOfToken lexerSpec))

run text = do
  val <- runProg text True
  putStrLn (show val)

runProg text bool = do 
  expressionAst <- parser text
  let expression = fromASTExp expressionAst

  if bool then putStrLn (show expression) else return ()
  
  let val = value_of_program expression      -- interpreter
  return val 

typecheck text = do
  let debugFlag = False
        
  expressionAst <-
    parsing debugFlag
       parserSpec ((), 1, 1, text)
       (aLexer lexerSpec)
       (fromToken (endOfToken lexerSpec))

  let expression = fromASTExp expressionAst
  
  putStrLn (show expression)

  eitherTyOrErr <- typeCheck expression
  case eitherTyOrErr of
    Right ty ->
      do putStrLn (show ty)

         let val = value_of_program expression
         putStrLn (show val)

    Left errMsg ->
      do putStrLn errMsg
