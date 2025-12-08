module Interp where

import Expr
import EnvStore

--
value_of :: ClassEnv -> Exp -> Env -> Store -> (ExpVal, Store)   

value_of class_env (Const_Exp n) env store = (Num_Val n,store)

value_of class_env (Var_Exp var) env store = 
  let (denval,store1) = apply_env env store var 
      loc = denval_loc denval
      val = deref store1 loc
  in  (val, store1)

value_of class_env (Diff_Exp exp1 exp2) env store =
  let (val1,store1) = value_of class_env exp1 env store
      (val2,store2) = value_of class_env exp2 env store1

      num1 = expval_num val1
      num2 = expval_num val2
  in  (Num_Val (num1 - num2), store2)

value_of class_env (Sum_Exp exp1 exp2) env store =
  let (val1,store1) = value_of class_env exp1 env store
      (val2,store2) = value_of class_env exp2 env store1

      num1 = expval_num val1
      num2 = expval_num val2
  in  (Num_Val (num1 + num2), store2)
  
value_of class_env (IsZero_Exp exp) env store =
  let (val1,store1) = value_of class_env exp env store in
    let num1 = expval_num val1 in
      if num1 == 0
      then (Bool_Val True,store1)
      else (Bool_Val False,store1)

value_of class_env (If_Exp exp1 exp2 exp3) env store =
  let (val1,store1) = value_of class_env exp1 env store in
    if expval_bool val1
    then value_of class_env exp2 env store1
    else value_of class_env exp3 env store1

value_of class_env (Let_Exp varExpList body) env store =
  let value_of_let_binding (varList, locList, store) (var,exp) =
        let (val,store') = value_of class_env exp env store
            (loc,store'') = newref store' val
        in  (varList++[var], locList++[loc], store'')

      (varList, locList, store') = 
        foldl value_of_let_binding ([], [], store) varExpList

      env' = extend_env varList locList env
  in value_of class_env body env' store'

value_of class_env (Letrec_Exp letbindings letrec_body) env store =
  value_of class_env letrec_body 
    (extend_env_rec (mkUntypedLetRecBindings letbindings) env) store

value_of class_env (Proc_Exp var body) env store =
  (Proc_Val (procedure var body env),store)

value_of class_env (Call_Exp rator rands) env store =
  let (val1,store1) = value_of class_env rator env store
      proc = expval_proc val1

      (args,store2) = foldl (value_of_arg class_env env) ([],store1) rands
  in apply_procedure proc args class_env store2

value_of class_env (Block_Exp exps) env store =
  let (vals,store1) = foldl value_of_each ([],store) exps
        where
          value_of_each (vals,store) exp =
            let (val,store') = value_of class_env exp env store in
              (vals++[val],store')
  in (last vals,store1)

value_of class_env (Set_Exp x exp) env store =
  let (val1,store1) = value_of class_env exp env store
      (denval,store2) = apply_env env store x
      loc = denval_loc denval
  in  (Num_Val 23,setref store2 loc val1)       -- The dummy value, 23, comes from the EOPL book. :)

value_of class_env (List_Exp exps) env store =
  let (vals,store1) = foldl value_of_each ([],store) exps
        where
          value_of_each (vals,store) exp =
            let (val,store') = value_of class_env exp env store in
              (vals++[val],store')
  in (List_Val vals,store1)

-- New kinds of expressions in classes

value_of class_env (Self_Exp) env store = 
  let (denval,store1) = apply_env env store "%self" 
      self_obj = denval_self denval
  in  (Object_Val self_obj, store1)

value_of class_env (Method_Call_Exp obj_exp method_name args) env store =
  let -- 수신 객체 평가
      (obj_val,store1) = value_of class_env obj_exp env store
      obj = expval_obj obj_val
      
      -- 인자들 평가
      (args_val,store2) = foldl (value_of_arg class_env env) ([],store1) args

      -- 동적 클래스 이름 및 정적 타입 조사
      dyn_class = object_class_name obj
      static_type = 
        case obj_exp of
          Var_Exp x -> let (den,_) = apply_env env store2 x
                       in case denval_type den of
                            Just (TyClass cname) -> Just cname
                            _                    -> Nothing
          _ -> Nothing
      
      -- 실제로 사용할 메서드 선택
      chosen_method =
        case static_type of
          Just cname -> 
            -- 정적 타입에서 먼저 메서드 찾기
            let m_static = find_method cname method_name class_env 
            in if method_is_static m_static
                then m_static  -- static이면 : "x의 정적 타입"에서 찾은 메서드 사용
                else find_method dyn_class method_name class_env  -- 아니면 : 동적 디스패치 -> 동적 클래스에서 다시 찾기
          Nothing ->
            -- 정적 타입을 모르면 그냥 dynamic dispatch
            find_method dyn_class method_name class_env

  in apply_method chosen_method obj args_val class_env store2

value_of class_env (Super_Call_Exp method_name args) env store =
  let (denval1,store1) = apply_env env store "%self" 
      self_obj = denval_self denval1
      (args_val,store2) = foldl (value_of_arg class_env env) ([],store1) args
      (denval2,store3) = apply_env env store2 "%super"
      super_class_name = denval_super denval2
  in apply_method 
      (find_method super_class_name method_name class_env) 
      self_obj args_val class_env store3

value_of class_env (New_Object_Exp class_name args) env store =
  let (args_val,store1) = foldl (value_of_arg class_env env) ([],store) args
      (obj,store2) = new_object class_name class_env store1
      (_, store3) = apply_method (find_method class_name "initialize" class_env)
                      obj args_val class_env store2
  in  (Object_Val obj, store3)

value_of class_env (Cast_Exp exp class_name) env store =
  let (val1,store1) = value_of class_env exp env store
      class_name1 = object_class_name (expval_obj val1)
  in  if is_subclass class_name1 class_name class_env
      then (val1,store1)
      else error $ "Invalid cast:" ++ class_name1 ++ " to " ++ class_name

value_of class_env (InstanceOf_Exp exp class_name) env store =      
  let (val1,store1) = value_of class_env exp env store
      class_name1 = object_class_name (expval_obj val1)
  in  if is_subclass class_name1 class_name class_env
      then (Bool_Val True,store1)
      else (Bool_Val False,store1)

-- Helper function for evaluating args
value_of_arg class_env env (vals,store) arg =
    let (val,store') = value_of class_env arg env store
    in  (vals++[val],store')
--
value_of_program :: Program -> ExpVal
value_of_program (Program classDecls body) =
  fst $ value_of init_class_Env body initEnv initStore
  where
    init_class_Env = initialize_class_env classDecls


--
-- initEnv in EnvStore.hs
--

--
-- initStore in EnvStore.hs

--
apply_procedure :: Proc -> [ExpVal] -> ClassEnv -> Store -> (ExpVal,Store)
apply_procedure proc args class_env store = 
  let (locs,store1) = foldl mkRefToArg ([], store) args
        where
          mkRefToArg (locs,store) arg = 
            let (loc,store') = newref store arg in
              (locs++[loc],store')
      
      vars = proc_vars proc   -- [(Type, Identifier)]
      ids = map snd vars
      tys = map fst vars
      env' = extend_env_with_type ids locs tys (saved_env proc)
  in
    value_of class_env (proc_body proc) env' store1

apply_method :: Method -> Object -> [ExpVal] -> ClassEnv -> Store -> (ExpVal, Store)
apply_method (AMethod isStatic vars (Just body) (Just super_name) field_names) self args class_env store = 
  let (refs_to_args, store') = 
        foldl mkRefToArg ([], store) args
        where
          mkRefToArg (refs_to_args,store) arg = 
            let (loc,store') = newref store arg in
              (refs_to_args++[loc],store')

      param_ids = map snd vars
      param_tys = map fst vars

      field_ids = map snd field_names
      field_tys = map fst field_names

      object_env = 
        extend_env_with_type param_ids refs_to_args param_tys   -- type과 저장
          (extend_env_with_self_and_super self super_name
            (extend_env_with_type field_ids (object_fields self) field_tys   -- type 과 저장
              empty_env))
        
  in value_of class_env body object_env store'

-- Utility
mkUntypedLetRecBindings :: LetRecBindings -> [ (Identifier, [(Type, Identifier)], Exp) ]  -- 인자 타입 정보는 유지
mkUntypedLetRecBindings = map (\(_,x,y,z) -> (x,y,z))

mkUntyped :: [(Type, Identifier)] -> [Identifier]
mkUntyped = map snd