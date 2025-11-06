{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Eta reduce" #-}
module TypeCheck where

import Expr
import TyEnv

--
typeCheck :: Program -> IO (Either String Type)
typeCheck program = return (type_of_program program )

--
add_module_defns_to_tyenv :: [ ModuleDef ] -> TyEnv -> Either String TyEnv
add_module_defns_to_tyenv [] tyenv = Right tyenv
add_module_defns_to_tyenv (ModuleDef m iface mbody : moddefs) tyenv = 
  do actual_iface <- interface_of mbody tyenv   -- 각 ModuleDef에 대해 실제 인터페이스 계산
     if sub_iface actual_iface iface tyenv      -- 주어진 인터페이스가 서브타입인지 검사
     then let newtyenv = extend_tyenv_with_module m iface tyenv in    -- 모듈이름 - 인터페이스 바인딩 추가
              add_module_defns_to_tyenv moddefs newtyenv 
     else Left $ "In the module " ++ m
                   ++ "\n  expected interface: " ++ show iface
                   ++ "\n  actual interface: " ++ show actual_iface

interface_of :: ModuleBody -> TyEnv -> Either String Interface 
interface_of (DefnsModuleBody defs) tyenv = 
  do decls <- defns_to_decls defs tyenv
     Right (SimpleIface decls)
interface_of (SubModuleBody (ModuleDef m iface subBody) restBody) tyenv =
  do actual_iface <- interface_of subBody tyenv -- 서브 모듈을 먼저 타입 체크
     if sub_iface actual_iface iface tyenv  -- 서브 모듈의 인터페이스 검사
      then do
        -- 서브 모듈이 추가된 타입 환경에서 기존 나머지 모듈 바디 계산
        let newtyenv = extend_tyenv_with_module m iface tyenv
        (SimpleIface rest_decls) <- interface_of restBody newtyenv
        -- 서브 모듈의 이름 : 인터페이스를 decls에 추가 
        let (SimpleIface sub_decls) = iface
            sub_iface_decls = SubIface m sub_decls
        Right (SimpleIface (sub_iface_decls : rest_decls))
        
      else -- 에러 처리
        Left $ "In the sub-module " ++ m
                   ++ "\n  expected interface: " ++ show iface
                   ++ "\n  actual interface: " ++ show actual_iface

defns_to_decls :: [ Definition ] -> TyEnv -> Either String [ Declaration ]
defns_to_decls [] tyenv = Right []
defns_to_decls (ValDefn var exp : defs) tyenv = 
  case type_of exp tyenv of
    Left errmsg -> Left $ errmsg ++ " in the declaration of " ++ var
    Right ty -> 
      do decls <- defns_to_decls defs (extend_tyenv var ty tyenv)
         Right (ValDecl var ty : decls)

sub_iface :: Interface -> Interface -> TyEnv -> Bool
sub_iface (SimpleIface decls1) (SimpleIface decls2) tyenv =
  sub_decls decls1 decls2 tyenv 

-- sub_decls :: [Declaration] -> [Declaration] -> TyEnv -> Bool
-- sub_decls decls1 [] tyenv = True 
-- sub_decls [] decls2 tyenv = False
-- sub_decls (ValDecl x ty1:decls1) (ValDecl y ty2:decls2) tyenv =
--   if x == y 
--   then if equalType ty1 ty2 
--         then sub_decls decls1 decls2 tyenv 
--         else False
--   else sub_decls decls1 (ValDecl y ty2:decls2) tyenv

sub_decls :: [Declaration] -> [Declaration] -> TyEnv -> Bool
sub_decls decls1 [] tyenv = True 
sub_decls [] decls2 tyenv = False
sub_decls (aDecl:as) (rDecl:rs) tyenv
 | is_match tyenv aDecl rDecl = sub_decls as rs tyenv
 | otherwise                  = sub_decls as (rDecl:rs) tyenv

is_match :: TyEnv -> Declaration -> Declaration -> Bool
is_match tyenv (ValDecl x ty1) (ValDecl y ty2) = 
  x == y && equalType ty1 ty2
is_match tyenv (SubIface x decls1) (SubIface y decls2) =
  x == y && sub_decls decls1 decls2 tyenv
is_match _ _ _ = False

--
type_of_program :: Program -> Either String Type
type_of_program program = 
  case program of 
    Program moddefs modbody ->
      case add_module_defns_to_tyenv moddefs empty_tyenv of
        Left errMsg -> Left errMsg
        Right tyenv -> type_of modbody tyenv
    
--
type_of :: Exp -> TyEnv -> Either String Type

type_of (Const_Exp n) tyenv = Right TyInt

type_of (Var_Exp var) tyenv = apply_tyenv tyenv var

type_of (QualifiedVar_Exp m v) tyenv =
  do (SimpleIface final_decls) <- lookup_nested_interface m tyenv
     lookup_var_in_decls v final_decls

type_of (Diff_Exp exp1 exp2) tyenv =
  do ty1 <- type_of exp1 tyenv 
     ty2 <- type_of exp2 tyenv 
     case ty1 of
       TyInt -> case ty2 of
                 TyInt -> Right TyInt
                 _     -> expectedButErr TyInt ty2 exp2
       _ -> expectedButErr TyInt ty1 exp1

type_of (IsZero_Exp exp1) tyenv =
  do ty1 <- type_of exp1 tyenv
     case ty1 of
       TyInt -> Right TyBool
       _     -> expectedButErr TyInt ty1 exp1

type_of exp@(If_Exp exp1 exp2 exp3) tyenv =
  do condTy <- type_of exp1 tyenv
     thenTy <- type_of exp2 tyenv
     elseTy <- type_of exp3 tyenv
     case condTy of
       TyBool -> if equalType thenTy elseTy
                 then Right thenTy
                 else inequalIfBranchTyErr thenTy elseTy exp2 exp
                      
       _      -> expectedButErr TyBool condTy exp1

type_of (Let_Exp var exp1 body) tyenv =
  do expTy  <- type_of exp1 tyenv 
     bodyTy <- type_of body (extend_tyenv var expTy tyenv) 
     Right bodyTy

type_of (Letrec_Exp ty proc_name bound_var bvar_ty proc_body letrec_body) tyenv =
  do let tyenv1 = extend_tyenv bound_var bvar_ty
                    (extend_tyenv proc_name (TyFun bvar_ty ty) tyenv)
     procbodyTy <- type_of proc_body tyenv1
     
     let tyenv2 = extend_tyenv proc_name (TyFun bvar_ty ty) tyenv
     letrecbodyTy <- type_of letrec_body tyenv2
     
     if equalType ty procbodyTy
       then Right letrecbodyTy
       else expectedButErr ty procbodyTy proc_body

type_of (Proc_Exp var argTy body) tyenv =
  do bodyTy <- type_of body (extend_tyenv var argTy tyenv)
     Right (TyFun argTy bodyTy)

type_of (Call_Exp rator rand) tyenv =
  do funTy <- type_of rator tyenv
     argTy <- type_of rand tyenv
     case funTy of
       TyFun ty1 ty2 -> if equalType ty1 argTy
                        then Right ty2
                        else inequalArgtyErr ty1 argTy rator rand
       _             -> expectedFuntyButErr funTy rator

         

-- Utilities
expectedButErr expectedTy gotTy exp =
  Left $ "Expected " ++ show expectedTy ++ " but got " ++ show gotTy ++ " in " ++ show exp

expectedFuntyButErr gotTy exp =
  Left $ "Expected function type but got " ++ show gotTy ++ " in " ++ show exp

inequalIfBranchTyErr thenTy elseTy exp2 exp3 =
  Left $ "Type mismatch: \n"
          ++ "\t" ++ show thenTy ++ " in " ++ show exp2
          ++ "\t" ++ show elseTy ++ " in " ++ show exp3

inequalArgtyErr argTy1 argTy2 funexp argexp =
  Left $ "Type mismatch: \n"
          ++ "\t" ++ show argTy1 ++ " for the arugment of " ++ show funexp
          ++ "\t" ++ show argTy2 ++ " in " ++ show argexp

equalType :: Type -> Type -> Bool
equalType TyInt  TyInt  = True
equalType TyBool TyBool = True
equalType (TyFun ty1 ty1') (TyFun ty2 ty2') =
  equalType ty1 ty2 && equalType ty1' ty2'
equalType _ _ = False

