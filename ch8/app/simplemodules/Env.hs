module Env where

import Expr (Identifier,Exp)
import Data.List (intersperse)

-- Environment
data Env =
    Empty_env
  | Extend_env Identifier ExpVal Env
  | Extend_env_rec Identifier Identifier Exp Env
  | Extend_env_with_module Identifier TypedModule Env

instance Show Env where
  show env = "[" ++ (concat $ intersperse "," $ showEnv env) ++ "]"

showEnv Empty_env = []
showEnv (Extend_env x v env) = (x ++ " = " ++ show v) : showEnv env
showEnv (Extend_env_rec f x _ env) = ("rec fun " ++ f) : showEnv env
showEnv (Extend_env_with_module m mod env) = (m ++ " " ++ show mod) : showEnv env

empty_env :: Env
empty_env = Empty_env

apply_env :: Env -> Identifier -> ExpVal
apply_env Empty_env search_var = error (search_var ++ " is not found.")
apply_env (Extend_env saved_var saved_val saved_env) search_var
  | search_var==saved_var = saved_val
  | otherwise             = apply_env saved_env search_var
apply_env (Extend_env_rec p_name b_var p_body saved_env) search_var
  | p_name==search_var = Proc_Val (procedure b_var p_body (Extend_env_rec p_name b_var p_body saved_env))
  | otherwise          = apply_env saved_env search_var
apply_env (Extend_env_with_module _ _ saved_env) search_var =
  apply_env saved_env search_var

extend_env :: Identifier -> ExpVal -> Env -> Env
extend_env x v env = Extend_env x v env

extend_env_rec :: Identifier -> Identifier -> Exp -> Env -> Env
extend_env_rec f x exp env = Extend_env_rec f x exp env

extend_env_with_module :: Identifier -> TypedModule -> Env -> Env
extend_env_with_module x mod env = Extend_env_with_module x mod env

lookup_qualified_var_in_env :: [Identifier] -> Identifier -> Env -> ExpVal
lookup_qualified_var_in_env mods var env =
  apply_env finalEnv var
  where finalEnv = foldl 
                      (\e m -> case lookup_module_name_in_env m e of
                                  SimpleModule e' -> e') env mods

lookup_module_name_in_env :: Identifier -> Env -> TypedModule
lookup_module_name_in_env mod_name Empty_env = error (mod_name ++ " is not found.")
lookup_module_name_in_env mod_name (Extend_env _ _ env) = lookup_module_name_in_env mod_name env
lookup_module_name_in_env mod_name (Extend_env_rec _ _ _ env) = lookup_module_name_in_env mod_name env
lookup_module_name_in_env mod_name (Extend_env_with_module saved_mod_name saved_mod env)
  | mod_name==saved_mod_name = saved_mod
  | otherwise                = lookup_module_name_in_env mod_name env

-- Typed modules
data TypedModule = SimpleModule Env deriving Show

-- Expressed values
data ExpVal =
    Num_Val {expval_num :: Int}
  | Bool_Val {expval_bool :: Bool}
  | Proc_Val {expval_proc :: Proc}

instance Show ExpVal where
  show (Num_Val num)   = show num
  show (Bool_Val bool) = show bool
  show (Proc_Val proc) = show "<proc>"

-- Denoted values
type DenVal = ExpVal   

-- Procedure values : data structures
data Proc = Procedure {var :: Identifier, body :: Exp, saved_env :: Env}

procedure :: Identifier -> Exp -> Env -> Proc
procedure var body env = Procedure var body env

-- In Interp.hs
-- apply_procedure :: Proc -> ExpVal -> ExpVal
  
