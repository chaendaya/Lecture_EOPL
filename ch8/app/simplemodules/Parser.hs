module Parser where

import CommonParserUtil
import Token
import Expr

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

      rule "ZeroOrMoreDeclaration -> " (\rhs -> return $ toASTDeclarationList []),

      rule "ZeroOrMoreDeclaration -> Declaration ZeroOrMoreDeclaration" (\rhs ->
        return $ toASTDeclarationList $ 
                  fromASTDeclaration (get rhs 1) : fromASTDeclarationList (get rhs 2)),

      rule "Declaration -> identifier : Type" (\rhs ->
        return $ toASTDeclaration (ValDecl (getText rhs 1) (fromASTType (get rhs 3)))),

      rule "Declaration -> identifier : Interface" (\rhs ->
        let id = getText rhs 1
            (SimpleIface decls) = fromASTInterface (get rhs 3)
        in return $ toASTDeclaration (SubIface id decls)),

      rule "ModuleBody -> ModuleDefinition ModuleBody" (\rhs ->
        return $ toASTModuleBody $
          SubModuleBody (fromASTModuleDef (get rhs 1))
                        (fromASTModuleBody (get rhs 2))),

      rule "ModuleBody -> [ ZeroOrMoreDefinition ]" (\rhs -> 
        return $ toASTModuleBody $ DefnsModuleBody (fromASTDefinitionList (get rhs 2))),

      rule "ZeroOrMoreDefinition -> " (\rhs -> return $ toASTDefinitionList []),

      rule "ZeroOrMoreDefinition -> Definition ZeroOrMoreDefinition" (\rhs -> 
        return $ toASTDefinitionList $
          fromASTDefinition (get rhs 1) : fromASTDefinitionList (get rhs 2) ),

      rule "Definition -> identifier = Expression" (\rhs -> 
        return $ toASTDefinition $ ValDefn (getText rhs 1) (fromASTExp (get rhs 3))),

      -- 다단계 QualifiedVar
      rule "Expression -> QualifiedVar" (\rhs ->
        return $ toASTExp $ fromASTExp (get rhs 1)),

      rule "QualifiedVar -> from identifier take QualifiedVar" (\rhs ->
        let m = getText rhs 2
            QualifiedVar_Exp mods x = fromASTExp (get rhs 4)
        in return $ toASTExp $ QualifiedVar_Exp (m:mods) x),

      rule "QualifiedVar -> from identifier take identifier" (\rhs ->
        let m = getText rhs 2
            x = getText rhs 4
        in return $ toASTExp $ QualifiedVar_Exp [m] x),

      -- rule "Expression -> from identifier take identifier" (\rhs -> 
      --   return $ toASTExp $ QualifiedVar_Exp (getText rhs 2) (getText rhs 4)),

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
        (\rhs -> return $ toASTType $ TyFun (fromASTType (get rhs 2)) (fromASTType (get rhs 4)))
    ],
    
    baseDir        = "./",
    actionTblFile  = "action_table_simplemodules.txt",
    gotoTblFile    = "goto_table_simplemodules.txt",
    grammarFile    = "prod_rules_simplemodules.txt",
    parserSpecFile = "mygrammar_simplemodules.grm",
    genparserexe   = "yapb-exe"
  }


