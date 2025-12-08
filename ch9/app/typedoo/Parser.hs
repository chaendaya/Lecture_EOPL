module Parser where

import CommonParserUtil
import Token
import Expr

-- | Utility
rule prodRule action              = (prodRule, action, Nothing  )
ruleWithPrec prodRule action prec = (prodRule, action, Just prec)

--
parserSpec :: ParserSpec Token PET IO ()
parserSpec = ParserSpec
  {
    startSymbol = "Program'",

    tokenPrecAssoc = [],

    parserSpecList =
    [
      {- Program : classes and an expression -}

      rule "Program' -> Program" (\rhs -> return $ get rhs 1),

      rule "Program -> ZeroMoreClassDecl Expression" 
        (\rhs -> return $ fromProgram $ 
                  Program (classDeclListFrom (get rhs 1)) (expFrom (get rhs 2))),

      rule "ZeroMoreClassDecl -> ClassDecl ZeroMoreClassDecl" 
        (\rhs -> return $ fromClassDeclList $ 
                  classDeclFrom (get rhs 1) : classDeclListFrom (get rhs 2)),

      rule "ZeroMoreClassDecl -> " (\rhs -> return $ fromClassDeclList []),

      rule "ClassDecl -> class identifier extends identifier ZeroMoreImplementsDecl ZeroMoreFieldDecl ZeroMoreMethodDecl"
        (\rhs -> return $ fromClassDecl $ 
                  Class_Decl (getText rhs 2) (getText rhs 4) 
                    (idListFrom (get rhs 5)) (typeIdListFrom (get rhs 6)) (methodDeclListFrom (get rhs 7))
               ),

      rule "ClassDecl -> interface identifier ZeroMoreAbstractMethodDecl" 
        (\rhs -> return $ fromClassDecl $
                  Interface_Decl (getText rhs 2) (methodDeclListFrom (get rhs 3))),
               
      rule "ZeroMoreImplementsDecl -> implements identifier ZeroMoreImplementsDecl" 
        (\rhs -> return $ fromIdList $ getText rhs 2 : idListFrom (get rhs 3)),

      rule "ZeroMoreImplementsDecl -> " 
               (\rhs -> return $ fromIdList []),        

      rule "ZeroMoreFieldDecl -> field Type identifier ZeroMoreFieldDecl" 
        (\rhs -> return $ fromTypeIdList
                  ((typeFrom (get rhs 2), getText rhs 3) : typeIdListFrom (get rhs 4))),

      rule "ZeroMoreFieldDecl -> " (\rhs -> return $ fromTypeIdList []),

      rule "ZeroMoreMethodDecl -> MethodDecl ZeroMoreMethodDecl" 
        (\rhs -> return $ fromMethodDeclList $ 
                  methodDeclFrom (get rhs 1) : methodDeclListFrom (get rhs 2)),

      rule "ZeroMoreMethodDecl -> " (\rhs -> return $ fromMethodDeclList []),

      rule "MethodDecl -> method Type identifier ( ZeroMoreTypedIdentifier ) Expression"
        (\rhs -> return $ fromMethodDecl $ 
                  Method_Decl False (typeFrom (get rhs 2)) (getText rhs 3) (typeIdListFrom (get rhs 5)) (expFrom (get rhs 7))),

      rule "MethodDecl -> staticmethod Type identifier ( ZeroMoreTypedIdentifier ) Expression"
        (\rhs -> return $ fromMethodDecl $ 
                  Method_Decl True (typeFrom (get rhs 2)) (getText rhs 3) (typeIdListFrom (get rhs 5)) (expFrom (get rhs 7))),

      rule "ZeroMoreAbstractMethodDecl -> AbstractMethodDecl ZeroMoreAbstractMethodDecl"
        (\rhs -> return $ fromMethodDeclList $
                  methodDeclFrom (get rhs 1) : methodDeclListFrom (get rhs 2)),
        
      rule "ZeroMoreAbstractMethodDecl -> " (\rhs -> return $ fromMethodDeclList []),

      rule "AbstractMethodDecl -> method Type identifier ( ZeroMoreTypedIdentifier )"
        (\rhs -> return $ fromMethodDecl $ 
                  AbstractMethod_Decl (typeFrom (get rhs 2)) (getText rhs 3) (typeIdListFrom (get rhs 5))),

      -- ZeroMoreTypedIdentifier :: PET_IdList
      rule "ZeroMoreTypedIdentifier -> OneMoreTypedIdentifier" (\rhs -> return $ get rhs 1),

      rule "ZeroMoreTypedIdentifier -> " (\rhs -> return $ fromTypeIdList []),

      rule "OneMoreTypedIdentifier -> identifier : Type , OneMoreTypedIdentifier" 
        (\rhs -> return $ fromTypeIdList $ (typeFrom (get rhs 3), getText rhs 1) : typeIdListFrom (get rhs 5)),

      rule "OneMoreTypedIdentifier -> identifier : Type"
        (\rhs -> return $ fromTypeIdList [ (typeFrom (get rhs 3), getText rhs 1) ]),
  

      {- Multiple expressions -}

      -- Exp1, Exp2, ... , Expk  (k >= 0)
      -- ZeroMoreExpression :: PET_ExpList
      rule "ZeroMoreExpression -> OneMoreExpression" (\rhs -> return $ get rhs 1),

      rule "ZeroMoreExpression -> " (\rhs -> return $ fromExpList []),

      -- Exp1, Exp2, ... , Expk  (k >= 1)  (separated by a comma)
      -- OneMoreExpression :: PET_ExpList  where length >= 1
      rule "OneMoreExpression -> Expression , OneMoreExpression" 
        (\rhs -> return $ fromExpList $ 
                  expFrom (get rhs 1) : expListFrom (get rhs 3)),

      rule "OneMoreExpression -> Expression" 
        (\rhs -> return $ fromExpList [ expFrom (get rhs 1) ]),

      -- Exp1 ; Exp2 ; ... ; Expk (k >= 0)   (separated by a semicolon)
      -- ExpressionList :: PET_ExpList
      rule "ExpressionList -> Expression"
        (\rhs -> return $ fromExpList [ expFrom (get rhs 1) ]),

      rule "ExpressionList -> Expression ; ExpressionList"
        (\rhs -> return $ fromExpList 
                  (expFrom (get rhs 1) : expListFrom (get rhs 3))),
      
      -- Exp1 Exp2 ... Expk  (separated by a space)
      -- ExpressionListSpace : PET_ExpList
      rule "ExpressionListSpace -> Expression"
        (\rhs -> return $ fromExpList [ expFrom (get rhs 1) ]),

      rule "ExpressionListSpace -> Expression ExpressionListSpace"
        (\rhs -> return $ fromExpList 
                  (expFrom (get rhs 1) : expListFrom (get rhs 3))),


      {- Single expression -}

      -- Expression :: PET_Exp 
      rule "Expression -> new identifier ( ZeroMoreExpression )"
        (\rhs -> return $ fromExp $ 
                    New_Object_Exp (getText rhs 2) (expListFrom (get rhs 4))),

      rule "Expression -> self" (\rhs -> return $ fromExp $ Self_Exp),

      rule "Expression -> send Expression identifier ( ZeroMoreExpression )"
        (\rhs -> return $ fromExp $ 
                    Method_Call_Exp (expFrom (get rhs 2)) 
                      (getText rhs 3) (expListFrom (get rhs 5)) ),

      rule "Expression -> super identifier ( ZeroMoreExpression )"
        (\rhs -> return $ fromExp $ 
                    Super_Call_Exp (getText rhs 2)  (expListFrom (get rhs 4)) ),

      rule "Expression -> cast Expression identifier"
        (\rhs -> return $ fromExp $ 
                    Cast_Exp (expFrom (get rhs 2)) (getText rhs 3)),

      rule "Expression -> instanceof Expression identifier"
        (\rhs -> return $ fromExp $ 
                    InstanceOf_Exp (expFrom (get rhs 2)) (getText rhs 3)),        

      rule "Expression -> integer_number"
        (\rhs -> return $ fromExp $ Const_Exp (read (getText rhs 1) :: Int)),
      
      rule "Expression -> - integer_number"
        (\rhs -> return $ fromExp $ Const_Exp (-(read (getText rhs 2) :: Int))),
      
      rule "Expression -> - ( Expression , Expression )"
        (\rhs -> return $ fromExp $ 
                  Diff_Exp (expFrom (get rhs 3)) (expFrom (get rhs 5))),

      rule "Expression -> + ( Expression , Expression )"
        (\rhs -> return $ fromExp $ 
                  Sum_Exp (expFrom (get rhs 3)) (expFrom (get rhs 5))),
  
      rule "Expression -> zero? ( Expression )"
        (\rhs -> return $ fromExp $ IsZero_Exp (expFrom (get rhs 3))),
      
      rule "Expression -> if Expression then Expression else Expression"
        (\rhs -> return $ fromExp $ 
                  If_Exp (expFrom (get rhs 2)) 
                    (expFrom (get rhs 4)) 
                    (expFrom (get rhs 6))),

      rule "Expression -> identifier" 
        (\rhs -> return $ fromExp $ Var_Exp (getText rhs 1)),
      
      rule "Expression -> let LetBindings in Expression"
        (\rhs -> return $ fromExp $ 
                  Let_Exp (idExpListFrom (get rhs 2)) (expFrom (get rhs 4))),

      rule "Expression -> letrec LetRecBindings in Expression"
        (\rhs -> return $ fromExp $ 
                  Letrec_Exp (typeIdTypeIdListExpListFrom (get rhs 2)) (expFrom (get rhs 4))),

      rule "Expression -> proc ( ZeroMoreTypedIdentifier ) Expression"
        (\rhs -> return $ fromExp $ 
                  Proc_Exp (typeIdListFrom (get rhs 3)) (expFrom (get rhs 5))),

      rule "Expression -> ( Expression ExpressionListSpace )"
        (\rhs -> return $ fromExp $ 
                  Call_Exp (expFrom (get rhs 2)) (expListFrom (get rhs 3))),

      rule "Expression -> begin ExpressionList end"
        (\rhs -> return $ fromExp $ 
                  Block_Exp (expListFrom (get rhs 2))),

      rule "Expression -> set identifier = Expression"
        (\rhs -> return $ fromExp $ 
                  Set_Exp (getText rhs 2) (expFrom (get rhs 4))),

      rule "Expression -> list ( ZeroMoreExpression )"
        (\rhs -> return $ fromExp $ 
                  List_Exp (expListFrom (get rhs 3))),

      {- Let bindings -}
      rule "LetBindings -> "
      (\rhs -> return $ fromIdExpList []),

      rule "LetBindings -> identifier = Expression LetBindings"
        (\rhs -> return $ fromIdExpList
                  ((getText rhs 1, expFrom (get rhs 3)) : idExpListFrom (get rhs 4))),

      {- Letrec bindings -}
      rule "LetRecBindings -> Type identifier ( ZeroMoreTypedIdentifier ) = Expression"
        (\rhs -> return $ fromTypeIdTypeIdListExpList 
                  [(typeFrom (get rhs 1), 
                    getText rhs 2, 
                    typeIdListFrom (get rhs 4), expFrom (get rhs 7))]),

      rule "LetRecBindings -> Type identifier ( ZeroMoreTypedIdentifier ) = Expression LetRecBindings"
        (\rhs -> return $ fromTypeIdTypeIdListExpList 
                  ((typeFrom (get rhs 1), 
                    getText rhs 2, 
                    typeIdListFrom (get rhs 4), 
                    expFrom (get rhs 7)) : typeIdTypeIdListExpListFrom (get rhs 8))),

      {- Types -}
      -- rule "ZeroMoreArgTypes -> " (\rhs -> return $ fromTypeList []),

      -- rule "ZeroMoreArgTypes -> OneMoreArgTypes" (\rhs -> return $ get rhs 1),

      rule "OneMoreArgTypes -> Type" (\rhs -> return $ fromTypeList [typeFrom (get rhs 1)]),

      rule "OneMoreArgTypes -> Type * OneMoreArgTypes" 
        (\rhs -> return $ fromTypeList $ typeFrom (get rhs 1) : tyListFrom (get rhs 3)),

      rule "Type -> int" (\rhs -> return $ fromType TyInt),

      rule "Type -> bool" (\rhs -> return $ fromType TyBool),

      rule "Type -> void" (\rhs -> return $ fromType TyVoid),

      rule "Type -> ( OneMoreArgTypes -> Type )" 
        (\rhs -> return $ fromType $ TyFun (tyListFrom (get rhs 2)) (typeFrom (get rhs 4))),

      rule "Type -> identifier" (\rhs -> return $ fromType $ TyClass (getText rhs 1)),

      rule "Type -> listof Type" (\rhs -> return $ fromType $ TyListOf (typeFrom (get rhs 2)))
    ],
    
    baseDir        = "./",
    actionTblFile  = "action_table_typedoo.txt",
    gotoTblFile    = "goto_table_typedoo.txt",
    grammarFile    = "prod_rules_typedoo.txt",
    parserSpecFile = "mygrammar_typedoo.grm",
    genparserexe   = "yapb-exe"
  }


