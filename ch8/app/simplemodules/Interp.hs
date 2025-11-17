module Interp where

import Expr
import Env

--
value_of :: Exp -> Env -> ExpVal

value_of (Const_Exp n) env = Num_Val n

value_of (Var_Exp var) env = apply_env env var

value_of (QualifiedVar_Exp mod var) env = lookup_qualified_var_in_env mod var env

value_of (Diff_Exp exp1 exp2) env =
  let val1 = value_of exp1 env
      val2 = value_of exp2 env

      num1 = expval_num val1
      num2 = expval_num val2
  in  Num_Val (num1 - num2)
  
value_of (IsZero_Exp exp) env =
  let val1 = value_of exp env in
    let num1 = expval_num val1 in
      if num1 == 0
      then Bool_Val True
      else Bool_Val False

value_of (If_Exp exp1 exp2 exp3) env =
  let val1 = value_of exp1 env in
    if expval_bool val1
    then value_of exp2 env
    else value_of exp3 env

value_of (Let_Exp var exp1 body) env =
  let val1 = value_of exp1 env in
    value_of body (extend_env var val1 env)

value_of (Letrec_Exp ty proc_name bound_var bvar_ty proc_body letrec_body) env =
  value_of letrec_body (extend_env_rec proc_name bound_var proc_body env)

value_of (Proc_Exp var ty body) env =
  Proc_Val (procedure var body env)

value_of (Call_Exp rator rand) env =
  apply_procedure proc arg
  where proc = expval_proc (value_of rator env)
        arg  = value_of rand env
  
--
add_module_defns_to_env :: [ModuleDef] -> Env -> Env
add_module_defns_to_env [] env = env
add_module_defns_to_env (ModuleDef mod_name _ mod_body : mod_defns) env =
  add_module_defns_to_env mod_defns (extend_env_with_module mod_name typed_mod env)
  where typed_mod = value_of_module_body mod_body env
  
value_of_module_body :: ModuleBody -> Env -> TypedModule
value_of_module_body (ModuleBody defs) env =
  SimpleModule (defns_to_env defs env)
-- value_of_module_body (DefnsModuleBody defs) env = 
--   SimpleModule (defns_to_env defs env)
-- value_of_module_body (SubModuleBody submod mod_body) env =
--   let ModuleDef sub_name _ sub_body = submod
--       sub_typed_mod = value_of_module_body sub_body env
--       new_env = extend_env_with_module sub_name sub_typed_mod env
--   in value_of_module_body mod_body new_env

defns_to_env :: [Definition] -> Env -> Env
defns_to_env [] env = empty_env
defns_to_env (ValDefn var exp : defns) env =
  let val = value_of exp env
      newenv = extend_env var val env 
  in extend_env var val (defns_to_env defns newenv)
defns_to_env (SubMod submod : defns) env =
  let ModuleDef sub_name _ sub_body = submod
      sub_typed_mod = value_of_module_body sub_body env
      newenv = extend_env_with_module sub_name sub_typed_mod env
  in extend_env_with_module sub_name sub_typed_mod (defns_to_env defns newenv)


--
value_of_program :: Program -> ExpVal

value_of_program (Program moddefs body) = 
  value_of body (add_module_defns_to_env moddefs empty_env)

--
apply_procedure :: Proc -> ExpVal -> ExpVal
apply_procedure proc arg =
   value_of (body proc) (extend_env (var proc) arg (saved_env proc))