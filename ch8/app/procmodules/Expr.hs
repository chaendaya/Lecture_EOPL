{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module Expr where

import Data.Maybe

-- for abstract syntax tree
data Program = Program [ ModuleDef ] Exp 
  deriving Show

data ModuleDef = ModuleDef Identifier Interface ModuleBody
  deriving Show

data ModuleBody = 
    DefnsModuleBody [ Definition ] 
  | ProcModuleBody Identifier Interface ModuleBody 
  | VarModuleBody Identifier
  | AppModuleBody ModuleBody ModuleBody
  -- | AppModuleBody Identifier Identifier
  deriving Show

data Interface = 
    SimpleIface [ Declaration ]
  | ProcIface Identifier Interface Interface
  deriving Show

data Declaration = 
    ValDecl Identifier Type 
  | OpaqueTypeDecl Identifier
  | TransparentTypeDecl Identifier Type
  deriving Show

name_of_decl :: Declaration -> Identifier
name_of_decl (ValDecl name _) = name
name_of_decl (OpaqueTypeDecl name) = name
name_of_decl (TransparentTypeDecl name _) = name

data Definition = 
    ValDefn Identifier Exp 
  | TypeDefn Identifier Type
  deriving Show

name_of_defn :: Definition -> Identifier
name_of_defn (ValDefn name _) = name
name_of_defn (TypeDefn name _) = name
  
data Exp =
    Const_Exp  Int
  | Diff_Exp   Exp Exp
  | IsZero_Exp Exp
  | If_Exp     Exp Exp Exp
  | Var_Exp    Identifier
  | Let_Exp    Identifier Exp Exp
  | Letrec_Exp Type Identifier Identifier Type Exp Exp -- letrec f(x) = ... recusive expr ...
  | Proc_Exp   Identifier Type Exp           -- proc
  | Call_Exp   Exp Exp                       -- call
  | QualifiedVar_Exp Identifier Identifier
  deriving Show

type Identifier = String

data Type =
    TyInt
  | TyBool
  | TyFun Type Type
  | TyName Identifier
  | TyQualified Identifier Identifier  -- module id, type id
  deriving (Show, Eq)

-- for parser
data AST =
    ASTExp { fromASTExp :: Exp }
  | ASTType { fromASTType :: Type }
  | ASTProgram { fromASTProgram :: Program }
  | ASTModuleDef { fromASTModuleDef :: ModuleDef }
  | ASTModuleDefList { fromASTModuleDefList :: [ModuleDef] }
  | ASTModuleBody { fromASTModuleBody :: ModuleBody }
  | ASTInterface { fromASTInterface :: Interface }
  | ASTDeclaration { fromASTDeclaration :: Declaration }
  | ASTDeclarationList { fromASTDeclarationList :: [Declaration] }
  | ASTDefinition { fromASTDefinition :: Definition }
  | ASTDefinitionList { fromASTDefinitionList :: [Definition] }
  deriving Show

toASTExp exp = ASTExp exp

toASTType ty = ASTType ty

toASTProgram prg = ASTProgram prg

toASTModuleDef md = ASTModuleDef md

toASTModuleDefList md = ASTModuleDefList md

toASTModuleBody mb = ASTModuleBody mb

toASTInterface itf = ASTInterface itf

toASTDeclaration decl = ASTDeclaration decl

toASTDeclarationList decl = ASTDeclarationList decl

toASTDefinition defn = ASTDefinition defn

toASTDefinitionList defn = ASTDefinitionList defn


-- for testing the type checker
-- type TestCaseName = String
-- type ExprText = String

-- data TypeDeclTestCase = TDTC TestCaseName ExprText (Maybe Type)

-- data TypeDeclTestSuite = TypeDeclTestSuite [ TypeDeclTestCase ]


