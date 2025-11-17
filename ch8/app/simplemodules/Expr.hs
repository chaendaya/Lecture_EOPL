module Expr where

import Data.Maybe

-- for abstract syntax tree
data Program = Program [ ModuleDef ] Exp 
  deriving Show

data ModuleDef = ModuleDef Identifier Interface ModuleBody
  deriving Show

-- data ModuleBody =
--     SubModuleBody ModuleDef ModuleBody
--   | DefnsModuleBody [Definition]
--   deriving Show
data ModuleBody = ModuleBody [Definition]
  deriving Show

data Definition = ValDefn Identifier Exp
              | SubMod ModuleDef
  deriving Show

data Interface = SimpleIface [Declaration]
  deriving Show

data Declaration = ValDecl Identifier Type 
                | SubIface Identifier [Declaration]
  deriving Show

-- data Definition = ValDefn Identifier Exp 
--   deriving Show

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
  | QualifiedVar_Exp [Identifier] Identifier
  deriving Show

type Identifier = String

data Type =
    TyInt
  | TyBool
  | TyFun Type Type
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


-- -- for testing the type checker
-- type TestCaseName = String
-- type ExprText = String

-- data TypeDeclTestCase = TDTC TestCaseName ExprText (Maybe Type)

-- data TypeDeclTestSuite = TypeDeclTestSuite [ TypeDeclTestCase ]


