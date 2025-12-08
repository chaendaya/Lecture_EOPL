{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Eta reduce" #-}
module EnvStore where

import Ref(Location)
import Expr (Identifier,Exp,Type,ClassDecl(..),MethodDecl(..))

import Data.Maybe
import Data.List (elemIndex,lookup)

-- Environment
data Env =
    Empty_env
  | Extend_env [Identifier] [Location] Env
  | Extend_env_with_type [Identifier] [Location] [Type] Env   -- typed 확장
  | Extend_env_rec [(Identifier,[(Type,Identifier)],Exp)] Env 
  | Extend_env_with_self_and_super Object Identifier Env

apply_env :: Env -> Store -> Identifier -> (DenVal, Store)
apply_env Empty_env store search_var = error (search_var ++ " is not found.")
apply_env (Extend_env saved_vars saved_vals saved_env) store search_var = 
  if search_var `elem` saved_vars
    then (Loc_Val (saved_vals !! (fromJust $ Data.List.elemIndex search_var saved_vars)) Nothing,store)
    else apply_env saved_env store search_var
apply_env (Extend_env_with_type saved_vars saved_vals saved_tys saved_env) store search_var =
  case elemIndex search_var saved_vars of
    Just i  -> (Loc_Val (saved_vals !! i) (Just (saved_tys !! i)), store)
    Nothing -> apply_env saved_env store search_var
apply_env (Extend_env_rec idIdExpList saved_env) store search_var
  | isIn      = let (l,store') = newref store procVal in (Loc_Val l Nothing, store')  -- 함수 이름 자체에는 타입 없이
  | otherwise = apply_env saved_env store search_var
  where isIn      = or [ p_name==search_var | (p_name,b_var,p_body) <- idIdExpList ]
        procVal = head [ Proc_Val (procedure b_var p_body (Extend_env_rec idIdExpList saved_env)) 
                       | (p_name,b_var,p_body) <- idIdExpList, p_name==search_var ]
apply_env (Extend_env_with_self_and_super obj super_name saved_env) store search_var
  | search_var == "%self"  = (SelfObject_Val obj,store)
  | search_var == "%super" = (SuperClassName_Val super_name, store)
  | otherwise = apply_env saved_env store search_var

-- Abstract data type interfaces for Env
empty_env :: Env
empty_env = Empty_env

extend_env :: [Identifier] -> [Location] -> Env -> Env
extend_env xs vs env = Extend_env xs vs env

extend_env_with_type :: [Identifier] -> [Location] -> [Type] -> Env -> Env
extend_env_with_type xs vs tys env = Extend_env_with_type xs vs tys env

extend_env_rec :: [(Identifier,[(Type, Identifier)],Exp)] -> Env -> Env
extend_env_rec idIdListExpList env = Extend_env_rec idIdListExpList env

extend_env_with_self_and_super :: Object -> Identifier -> Env -> Env
extend_env_with_self_and_super obj super_name env = 
  Extend_env_with_self_and_super obj super_name env

-- Expressed values
data ExpVal =
    Num_Val {expval_num :: Int}
  | Bool_Val {expval_bool :: Bool}
  | Proc_Val {expval_proc :: Proc}
  -- | Ref_Val {expval_loc :: Location}
  | List_Val {expval_list :: [ExpVal]} -- Listof_Val?
  | Object_Val  {expval_obj :: Object}
  | Uninitialized_Val  -- for uninitialized fields (Not in the textbook)

instance Show ExpVal where
  show (Num_Val num)   = show num
  show (Bool_Val bool) = show bool
  show (Proc_Val proc) = show proc  -- "<proc>"
  show (List_Val list) = "(" ++ showWithSp list ++ ")" -- Todo: print a list as [1,2,3] instead of (1,2,3)??
  show (Object_Val obj) = show obj
  show (Uninitialized_Val) = "<uninitialized>"

showWithSp :: [ExpVal] -> String
showWithSp [] = ""
showWithSp [x] = show x
showWithSp (x:xs) = show x ++ " " ++ showWithSp xs  

-- Denoted values
data DenVal = 
    Loc_Val {denval_loc :: Location, denval_type :: Maybe Type} -- Ref(ExpVal) , 정적 타입
  | SelfObject_Val {denval_self :: Object} -- for %self
  | SuperClassName_Val {denval_super :: Identifier} -- for %super

-- Procedure values : data structures
data Proc = Procedure {proc_vars :: [(Type, Identifier)], proc_body :: Exp, saved_env :: Env}   -- Type 포함

instance Show Proc where
  show (Procedure vars body saved_env) = show "<proc>"

procedure :: [(Type, Identifier)] -> Exp -> Env -> Proc
procedure vars body env = Procedure vars body env

-- Object values : data structures
data Object = AnObject {object_class_name :: Identifier, object_fields :: [Location]}

instance Show Object where
  show (AnObject class_name fields) = 
    "<" ++ show class_name ++ ":object>"

-- In Interp.hs
-- apply_procedure :: Proc -> ExpVal -> ExpVal
  
-- | Store.hs
type Store = (Location, [(Location,ExpVal)]) -- Next new location

newref :: Store -> ExpVal -> (Location,Store)
newref (next,s) v = (next,(next+1,(next,v):s))

deref :: Store -> Location -> ExpVal
deref (next,s) loc =
  case [v | (loc',v) <- s, loc==loc'] of
    (v:_) -> v
    _     -> error ("Location not found: " ++ show loc)

setref :: Store -> Location -> ExpVal -> Store
setref (next,s) loc v = (next,update s)
  where update [] = error ("Invalid reference: " ++ show loc)
        update ((loc',w):s')
          | loc==loc' = (loc,v):s'
          | otherwise = (loc',w):update s'

--
initEnv :: Env
initEnv = extend_env ["i", "v", "x"] [1,2,3] empty_env

initStore :: Store
initStore = (4,[(1, Num_Val 1)
                , (2, Num_Val 5)
                , (3, Num_Val 10)])

-- Classes
data Class = 
   AClass { class_super_name :: Maybe Identifier, 
            class_field_names :: [(Type, Identifier)], 
            class_method_env :: MethodEnv}
  | AnInterface 
          { interface_name :: Identifier, 
            interface_method_env :: MethodEnv }

new_object :: Identifier -> ClassEnv -> Store -> (Object, Store)
new_object class_name class_env store = 
  let field_names = class_field_names (lookup_class class_name class_env)
      (objFields, store') = 
        foldl mkUninitializedFields ([], store) field_names
        where
          mkUninitializedFields (fields,store) field_name = 
            let (loc,store') = newref store Uninitialized_Val in
              (fields++[loc],store')             
  in (AnObject class_name objFields, store')

-- Methods
data Method = AMethod 
  { method_is_static :: Bool,   -- isStatic
    method_vars :: [(Type, Identifier)], 
    method_body :: Maybe Exp,
    method_super_name :: Maybe Identifier,
    method_field_names :: [(Type, Identifier)]
  }

  -- abstract method: method_body = Nothing, method_field_names = [] 

-- apply_method in Interp.hs

-- Class Environments
type ClassEnv = [ (Identifier,Class) ]

initClassEnv :: ClassEnv
initClassEnv = [ ("object", AClass Nothing [] []) ]

add_to_class_env :: Identifier -> Class -> ClassEnv -> ClassEnv
add_to_class_env class_name aClass class_env = 
  (class_name,aClass) : class_env

lookup_class :: Identifier -> ClassEnv -> Class
lookup_class class_name class_env = 
  case Data.List.lookup class_name class_env of
    Just aClass -> aClass
    Nothing    -> error ("Class " ++ class_name ++ " not found.")

initialize_class_env :: [ClassDecl] -> ClassEnv
initialize_class_env classDecls = 
  foldl (flip initialize_class_decl) initClassEnv classDecls    

initialize_class_decl :: ClassDecl -> ClassEnv -> ClassEnv
initialize_class_decl (Class_Decl class_name super_name ifaces field_names method_decls) class_env = 
  let accumulated_field_names = 
        append_field_names
          (class_field_names (lookup_class super_name class_env))
          field_names
      aClass = AClass (Just super_name) accumulated_field_names
                  (merge_method_envs 
                    (class_method_env (lookup_class super_name class_env)) 
                      (method_decls_method_envs 
                        method_decls (Just super_name) accumulated_field_names))
  in add_to_class_env class_name aClass class_env

initialize_class_decl (Interface_Decl iface_name method_decls) class_env = 
  let anIface = AnInterface iface_name (method_decls_method_envs method_decls Nothing [])
  in add_to_class_env iface_name anIface class_env

append_field_names :: [(Type, Identifier)] -> [(Type, Identifier)] -> [(Type, Identifier)]
append_field_names super_fields new_fields =
  rename_super_fields 1 super_fields
  where
    rename_super_fields n [] = new_fields
    rename_super_fields n ((ty,f):fs)
      | f `elem'` new_fields = (ty, f ++ "_" ++ show n) : rename_super_fields (n+1) fs
      | otherwise           = (ty,f) : rename_super_fields n fs

    elem' :: Identifier -> [(Type, Identifier)] -> Bool
    elem' f [] = False
    elem' f ((_,f'):fs) = f == f' || elem' f fs

-- Method Environments
type MethodEnv = [ (Identifier, Method)]

find_method :: Identifier -> Identifier -> ClassEnv -> Method
find_method class_name method_name class_env = 
  let aClass = lookup_class class_name class_env 
      methodEnv = class_method_env aClass
  in case Data.List.lookup method_name methodEnv of
      Just method -> method
      Nothing     -> error ("Method " ++ method_name ++ " not found.")

method_decls_method_envs :: [MethodDecl] -> Maybe Identifier -> [(Type, Identifier)] -> MethodEnv
method_decls_method_envs method_decls maybe_super_name field_names = 
  map method_decl_method_env method_decls
  where
    method_decl_method_env (Method_Decl isStatic ty method_name vars body) =  -- isStatic 전달
      (method_name, AMethod isStatic vars (Just body) maybe_super_name field_names)

merge_method_envs :: MethodEnv -> MethodEnv -> MethodEnv
merge_method_envs superMethodEnvs newMethodEnvs = newMethodEnvs ++ superMethodEnvs

-- 
is_subclass :: Identifier -> Identifier -> ClassEnv -> Bool
is_subclass class_name1 class_name2 class_env = 
  if class_name1 == class_name2
    then True
    else case class_super_name (lookup_class class_name1 class_env) of
            Just super_name -> is_subclass super_name class_name2 class_env
            Nothing         -> False  