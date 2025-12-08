module Expr(Program(..),ClassDecl(..),MethodDecl(..),Exp(..),Identifier,
            PET(..), Type(..), self, initialize,
            fromExp,fromType,
            fromExpList,fromIdExpList,fromTypeIdTypeIdListExpList,fromIdList,fromTypeList,fromTypeIdList,
            fromClassDecl,fromClassDeclList,fromMethodDecl,fromMethodDeclList,
            fromProgram,
            LetRecBindings, idFromMethodDecl) where

-- Untyped class-based expression language

data Program = Program [ClassDecl] Exp
  deriving Show
  
-- Class_Decl: class-name, super-class-name, interface-names, types and field-names, method-decls
data ClassDecl = 
    Class_Decl Identifier Identifier [Identifier] [ (Type, Identifier) ] [ MethodDecl ]
  | Interface_Decl Identifier [ MethodDecl ]
  deriving Show

-- Method_Decl: return type, method-name, parameter-types and names, body
data MethodDecl = 
    Method_Decl Bool Type Identifier [ (Type, Identifier) ] Exp  -- isStatic
  | AbstractMethod_Decl Type Identifier [ (Type, Identifier) ]  
  deriving Show

idFromMethodDecl (Method_Decl _ _ mName _ _)        = mName
idFromMethodDecl (AbstractMethod_Decl _ mName _) = mName

data Exp =
    Const_Exp  Int
  | Diff_Exp   Exp Exp
  | Sum_Exp    Exp Exp
  | IsZero_Exp Exp
  | If_Exp     Exp Exp Exp
  | Var_Exp    Identifier
  | Let_Exp    LetBindings Exp    -- let bindings in expr
  | Letrec_Exp LetRecBindings Exp -- letrec rec_bindings in expr
  | Proc_Exp   [ (Type, Identifier) ] Exp   -- proc
  | Call_Exp   Exp [Exp]          -- e1 e2 ... en (n >= 1)
  | Block_Exp  [Exp]
  | Set_Exp    Identifier Exp
  | List_Exp   [Exp]              -- list(e1, ..., en)

  -- New kinds of expressions in classes
  | New_Object_Exp Identifier [Exp]      -- new Identifier ( Exp1, ..., Expn )
  | Method_Call_Exp Exp Identifier [Exp] -- Exp.Identifier ( Exp1, ..., Expn )
  | Super_Call_Exp Identifier [Exp]      -- super.Identifier ( Exp1, ..., Expn )
  | Self_Exp                             -- self
  | Cast_Exp Exp Identifier              -- (Type) Exp
  | InstanceOf_Exp Exp Identifier        -- Exp instanceof Identifier
  deriving Show  

type Identifier = String

self :: Identifier
self = "self"

initialize :: Identifier
initialize = "initialize"

-- x1 = expr1  ...  xn = exprn
type LetBindings = [ (Identifier, Exp) ]  

-- f1(x11,...,xn1) = expr1  ...  fk(xk1,...,xkn) = exprk
type LetRecBindings = [(Type, Identifier, [ (Type, Identifier) ], Exp)] 

data Type =
    TyInt
  | TyBool
  | TyVoid
  | TyFun [Type] Type
  | TyClass Identifier  -- class name or interface name
  | TyListOf Type -- listof(type)
  deriving (Eq, Show)


--- Parsed Expression Tree

data PET =
    PET_TypeIdTypeIdListExpList {typeIdTypeIdListExpListFrom :: [(Type, Identifier, [(Type, Identifier)], Exp)] }
  | PET_IdExpList {idExpListFrom :: [(Identifier, Exp)] }
  | PET_ExpList {expListFrom :: [Exp] }
  | PET_Exp {expFrom :: Exp}
  | PET_Type {typeFrom :: Type}
  | PET_IdList {idListFrom :: [Identifier] }
  | PET_TypeList {tyListFrom :: [Type] }
  | PET_TypeIdList {typeIdListFrom :: [(Type, Identifier)] }
  | PET_MethodDecl {methodDeclFrom :: MethodDecl}
  | PET_MethodDeclList {methodDeclListFrom :: [MethodDecl]}
  | PET_ClassDecl {classDeclFrom :: ClassDecl}
  | PET_ClassDeclList {classDeclListFrom :: [ClassDecl]}
  | PET_Program {programFrom :: Program}
  deriving Show

fromExp exp                 = PET_Exp exp
fromType ty                 = PET_Type ty
fromExpList expList         = PET_ExpList expList
fromIdExpList idExpList     = PET_IdExpList idExpList

fromTypeIdTypeIdListExpList typeIdTypeIdListExpList 
                            = PET_TypeIdTypeIdListExpList typeIdTypeIdListExpList
fromIdList idList           = PET_IdList idList
fromTypeList tyList         = PET_TypeList tyList
fromTypeIdList typeIdList   = PET_TypeIdList typeIdList
fromMethodDecl methodDecl   = PET_MethodDecl methodDecl
fromClassDecl classDecl     = PET_ClassDecl classDecl
fromMethodDeclList methodDeclList = PET_MethodDeclList methodDeclList
fromClassDeclList classDeclList   = PET_ClassDeclList classDeclList
fromProgram program         = PET_Program program


-- for testing the type checker
-- type TestCaseName = String
-- type ExprText = String

-- data TypeDeclTestCase = TDTC TestCaseName ExprText (Maybe Type)

-- data TypeDeclTestSuite = TypeDeclTestSuite [ TypeDeclTestCase ]