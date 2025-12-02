module Parser where

import CommonParserUtil
import Token
import Expr
import Expr (AST(fromASTType))

-- | Utility
rule prodRule action              = (prodRule, action, Nothing  )
ruleWithPrec prodRule action prec = (prodRule, action, Just prec)

--
parserSpec :: ParserSpec Token AST IO ()
parserSpec = ParserSpec
  {
    startSymbol = "Program'",

    tokenPrecAssoc = [],

    parserSpecList =
    [
      rule "Program' -> Program" (\rhs -> return $ get rhs 1),

      rule "Program -> ZeroOrMoreModuleDefinition Expression" (\rhs -> 
        return $ 
          toASTProgram $ 
            Program (fromASTModuleDefList (get rhs 1)) (fromASTExp (get rhs 2))),

      rule "ZeroOrMoreModuleDefinition -> " (\rhs -> return $ toASTModuleDefList []),

      rule "ZeroOrMoreModuleDefinition -> ModuleDefinition ZeroOrMoreModuleDefinition"
        (\rhs -> return $ toASTModuleDefList $ 
            ( fromASTModuleDef (get rhs 1) : fromASTModuleDefList (get rhs 2)) ),

      rule "ModuleDefinition -> module identifier interface Interface body ModuleBody"
        (\rhs -> return $ toASTModuleDef $ 
            (ModuleDef (getText rhs 2)
                        (fromASTInterface (get rhs 4))
                          (fromASTModuleBody (get rhs 6)))),

      rule "Interface -> [ ZeroOrMoreDeclaration ]" (\rhs ->
        return $ toASTInterface $ SimpleIface (fromASTDeclarationList (get rhs 2))),

      rule "Interface -> ( ( identifier : Interface ) => Interface )" (\rhs ->
        return $ toASTInterface $ 
                  ProcIface (getText rhs 3) 
                    (fromASTInterface (get rhs 5))
                    (fromASTInterface (get rhs 8))),

      rule "ZeroOrMoreDeclaration -> " (\rhs -> return $ toASTDeclarationList []),

      rule "ZeroOrMoreDeclaration -> Declaration ZeroOrMoreDeclaration" (\rhs ->
        return $ toASTDeclarationList $ 
                  fromASTDeclaration (get rhs 1) : fromASTDeclarationList (get rhs 2)),

      rule "Declaration -> identifier : Type" (\rhs ->
        return $ toASTDeclaration (ValDecl (getText rhs 1) (fromASTType (get rhs 3)))),

      rule "Declaration -> opaque identifier" (\rhs ->
        return $ toASTDeclaration (OpaqueTypeDecl (getText rhs 2))),

      rule "Declaration -> transparent identifier = Type" (\rhs ->
        return $ toASTDeclaration (TransparentTypeDecl (getText rhs 2) (fromASTType (get rhs 4)))),

      rule "ModuleBody -> [ ZeroOrMoreDefinition ]" (\rhs -> 
        return $ toASTModuleBody $ DefnsModuleBody (fromASTDefinitionList (get rhs 2))),

      rule "ModuleBody -> module_proc ( identifier : Interface ) ModuleBody" (\rhs ->
        return $ toASTModuleBody $ 
                    ProcModuleBody
                      (getText rhs 3) 
                        (fromASTInterface (get rhs 5))
                          (fromASTModuleBody (get rhs 7)) ),

      rule "ModuleBody -> identifier" (\rhs -> 
        return $ toASTModuleBody $ VarModuleBody (getText rhs 1)),

      rule "ModuleBody -> ( ModuleBody ModuleBody )" (\rhs -> do
        let rator = fromASTModuleBody (get rhs 2)
            rand = fromASTModuleBody (get rhs 3) 
        return $ toASTModuleBody $ AppModuleBody rator rand),

      -- rule "ModuleBody -> ( identifier identifier )" (\rhs -> 
      --   return $ toASTModuleBody $ AppModuleBody (getText rhs 2) (getText rhs 3)),

      rule "ZeroOrMoreDefinition -> " (\rhs -> return $ toASTDefinitionList []),

      rule "ZeroOrMoreDefinition -> Definition ZeroOrMoreDefinition" (\rhs -> 
        return $ toASTDefinitionList $
          fromASTDefinition (get rhs 1) : fromASTDefinitionList (get rhs 2) ),

      rule "Definition -> identifier = Expression" (\rhs -> 
        return $ toASTDefinition $ ValDefn (getText rhs 1) (fromASTExp (get rhs 3))),

      rule "Definition -> type identifier = Type" (\rhs -> 
        return $ toASTDefinition $ TypeDefn (getText rhs 2) (fromASTType (get rhs 4))),

      rule "Expression -> from identifier take identifier" (\rhs -> 
        return $ toASTExp $ QualifiedVar_Exp (getText rhs 2) (getText rhs 4)),

      rule "Expression -> integer_number"
        (\rhs -> return $ toASTExp $ Const_Exp (read (getText rhs 1) :: Int)),
      
      rule "Expression -> - integer_number"
        (\rhs -> return $ toASTExp $ Const_Exp (-(read (getText rhs 2) :: Int))),
      
      rule "Expression -> - ( Expression , Expression )"
        (\rhs -> return $ toASTExp $ Diff_Exp (fromASTExp $ get rhs 3) (fromASTExp $ get rhs 5)),

      rule "Expression -> zero? ( Expression )"
        (\rhs -> return $ toASTExp $ IsZero_Exp (fromASTExp $ get rhs 3)),
      
      rule "Expression -> if Expression then Expression else Expression"
        (\rhs -> return $ toASTExp $ If_Exp (fromASTExp $ get rhs 2) (fromASTExp $ get rhs 4) (fromASTExp $ get rhs 6)),

      rule "Expression -> identifier" (\rhs -> return $ toASTExp $ Var_Exp (getText rhs 1)),
      
      rule "Expression -> let identifier = Expression in Expression"
        (\rhs -> return $ toASTExp $ Let_Exp (getText rhs 2) (fromASTExp $ get rhs 4) (fromASTExp $ get rhs 6)),

      rule "Expression -> letrec Type identifier ( identifier : Type ) = Expression in Expression"
        (\rhs -> return $ toASTExp $ Letrec_Exp (fromASTType $ get rhs 2) (getText rhs 3) (getText rhs 5) (fromASTType $ get rhs 7) (fromASTExp $ get rhs 10) (fromASTExp $ get rhs 12)),

      rule "Expression -> proc ( identifier : Type ) Expression"
        (\rhs -> return $ toASTExp $ Proc_Exp (getText rhs 3) (fromASTType $ get rhs 5) (fromASTExp $ get rhs 7)),

      rule "Expression -> ( Expression Expression )"
        (\rhs -> return $ toASTExp $ Call_Exp (fromASTExp $ get rhs 2) (fromASTExp $ get rhs 3)),
        
      rule "Type -> int"
        (\rhs -> return $ toASTType $ TyInt),
      
      rule "Type -> bool"
        (\rhs -> return $ toASTType $ TyBool),
      
      rule "Type -> ( Type -> Type )"
        (\rhs -> return $ toASTType $ TyFun (fromASTType (get rhs 2)) (fromASTType (get rhs 4))),

      rule "Type -> identifier" (\rhs -> return $ toASTType (TyName (getText rhs 1))), 

      rule "Type -> from identifier take identifier" (\rhs -> 
        return $ toASTType (TyQualified (getText rhs 2) (getText rhs 4)))
    ],
    
    baseDir        = "./",
    actionTblFile  = "action_table_procmodules.txt",
    gotoTblFile    = "goto_table_procmodules.txt",
    grammarFile    = "prod_rules_procmodules.txt",
    parserSpecFile = "mygrammar_procmodules.grm",
    genparserexe   = "yapb-exe"
  }


