module TyEnv where

import Expr(Identifier, Type, Interface(..), Declaration(..))

data TyEnv = 
    Empty_tyenv
  | Extend_tyenv Identifier Type TyEnv
  | Extend_tyenv_with_module Identifier Interface TyEnv

empty_tyenv :: TyEnv
empty_tyenv = Empty_tyenv

extend_tyenv :: Identifier -> Type -> TyEnv -> TyEnv
extend_tyenv var ty tyenv = Extend_tyenv var ty tyenv 

extend_tyenv_with_module mod_var iface tyenv = 
  Extend_tyenv_with_module mod_var iface tyenv

apply_tyenv :: TyEnv -> Identifier -> Either String Type 
apply_tyenv Empty_tyenv var = Left $ "Variable not found: " ++ var
apply_tyenv (Extend_tyenv v ty tyenv) var
  | var == v = Right ty
  | otherwise = apply_tyenv tyenv var

-- lookup_qualified_var_in_tyenv :: Identifier -> Identifier -> TyEnv -> Either String Type
-- lookup_qualified_var_in_tyenv mod_var var tyenv =
--   do iface <- lookup_module_name_in_tyenv tyenv mod_var 
--      case iface of
--        SimpleIface decls -> 
--          lookup_variable_name_in_decls var decls

lookup_nested_interface :: [Identifier] -> TyEnv -> Either String Interface
lookup_nested_interface (mod_head:mod_tail) tyenv = do 
  (SimpleIface decls) <- lookup_module_name_in_tyenv tyenv mod_head
  lookup_decls mod_tail decls

lookup_decls :: [Identifier] -> [Declaration] -> Either String Interface
lookup_decls [] decls = Right $ SimpleIface decls
lookup_decls (m:ms) decls =
  case decls of
    (SubIface name sub_decls : rest) ->
      if name == m 
      then lookup_decls ms sub_decls
      else lookup_decls (m:ms) rest
    (ValDecl _ _ : rest) -> lookup_decls (m:ms) rest
    [] -> Left $ "lookup_decls: module " ++ m ++ " not found"

lookup_var_in_decls :: Identifier -> [Declaration] -> Either String Type
lookup_var_in_decls var [] = Left $ "lookup_var_in_decls: variable " ++ var ++ " not found"
lookup_var_in_decls var (ValDecl x ty: decls)
  | var == x = Right ty
  | otherwise = lookup_var_in_decls var decls
lookup_var_in_decls var (SubIface _ _ : decls) = lookup_var_in_decls var decls

lookup_module_name_in_tyenv :: TyEnv -> Identifier -> Either String Interface
lookup_module_name_in_tyenv Empty_tyenv mod_var = 
  Left $ "lookup_module_name_in_tyenv: " ++ mod_var ++ " not found"
lookup_module_name_in_tyenv (Extend_tyenv _ _ tyenv) mod_var = 
  lookup_module_name_in_tyenv tyenv mod_var
lookup_module_name_in_tyenv (Extend_tyenv_with_module m iface tyenv) mod_var
  | m == mod_var = Right iface 
  | otherwise = lookup_module_name_in_tyenv tyenv mod_var

