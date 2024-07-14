
-- The syntax is based on the implicitrefs language, and
-- the semantics is based on the one for the continuation-based language.

module Interp where

import Expr
import EnvStore
import Semaphores
import Scheduler

import Debug.Trace

-- Continuation

data Cont =
    End_Main_Thread_Cont
  | Zero1_Cont Cont
  | Let_Exp_Cont Identifier Exp Env Cont
  | If_Test_Cont Exp Exp Env Cont
  | Diff1_Cont Exp Env Cont
  | Diff2_Cont ExpVal Cont
  | Rator_Cont Exp Env Cont
  | Rand_Cont ExpVal Cont
  | Unop_Arg_Cont UnaryOp Cont
  | Set_Rhs_Cont Location Cont
  | Spawn_Cont Cont
  | Wait_Cont Cont
  | Signal_Cont Cont
  | End_Subthread_Cont

apply_cont :: Store -> SchedState -> Cont -> ExpVal -> (FinalAnswer, Store)
apply_cont store sched cont val =
  if time_expired sched
  then
    let sched' = place_on_ready_queue
                   (\store0 sched0 -> apply_cont store0 sched0 cont val)
                   sched
    in  run_next_thread store sched'
    
  else
    let sched' = decrement_timer sched
    in  apply_cont' store sched' cont val
    
  where
    apply_cont' store sched End_Main_Thread_Cont v =
      let sched' = set_final_answer sched v in 
        run_next_thread store sched'

    apply_cont' store sched (Zero1_Cont cont) num1 =
      apply_cont store sched cont
        (if expval_num num1 == 0
         then Bool_Val True
         else Bool_Val False)

    apply_cont' store sched (Let_Exp_Cont var body env cont) val1 =
      let (loc,store') = newref store val1
      in  value_of_k body (extend_env var loc env) cont store' sched

    apply_cont' store sched (If_Test_Cont exp2 exp3 env cont) v =
      if expval_bool v
      then value_of_k exp2 env cont store sched
      else value_of_k exp3 env cont store sched

    apply_cont' store sched (Diff1_Cont exp2 env cont) val1 =
      value_of_k exp2 env (Diff2_Cont val1 cont) store sched

    apply_cont' store sched (Diff2_Cont val1 cont) val2 =
      let num1 = expval_num val1
          num2 = expval_num val2
      in  apply_cont store sched cont (Num_Val (num1 - num2))

    apply_cont' store sched (Unop_Arg_Cont op cont) val =
      let res = apply_unop op val in
        res `seq` apply_cont store sched cont res

    apply_cont' store sched (Rator_Cont rand env cont) ratorVal =
      value_of_k rand env (Rand_Cont ratorVal cont) store sched 

    apply_cont' store sched (Rand_Cont ratorVal cont) randVal =
      let proc = expval_proc ratorVal in
        apply_procedure_k proc randVal store sched cont

    apply_cont' store sched (Set_Rhs_Cont loc cont) val =
      let store' = setref store loc val in
        apply_cont store' sched cont (Num_Val 23)

    apply_cont' store sched (Spawn_Cont saved_cont) val =
      let proc1 = expval_proc val
          sched' = place_on_ready_queue
                       (\store sched ->
                          apply_procedure_k proc1 (Num_Val 28) store sched End_Subthread_Cont)
                       sched
      in  apply_cont store sched' saved_cont (Num_Val 73) 

    apply_cont' store sched (Wait_Cont saved_cont) val =
      wait_for_mutex (expval_mutex val)
        (\store1 sched1 -> apply_cont store1 sched1 saved_cont (Num_Val 52)) store sched

    apply_cont' store sched (Signal_Cont saved_cont) val =
      signal_mutex (expval_mutex val)
        (\store1 sched1 -> apply_cont store1 sched1 saved_cont (Num_Val 53)) store sched

    apply_cont' store sched (End_Subthread_Cont) val =
      run_next_thread store sched

-- Todo: Introduce exceptions and define apply_handler to see how complex it is!
-- Todo: Use the monadic style to hide as many global parameters as possible.

apply_unop :: UnaryOp -> ExpVal -> ExpVal

apply_unop IsZero (Num_Val num)
  | num==0    = Bool_Val True
  | otherwise = Bool_Val False
apply_unop IsNull (List_Val [])  = Bool_Val True
apply_unop IsNull (List_Val _)   = Bool_Val False
apply_unop Car (List_Val (x:_))  = x
apply_unop Cdr (List_Val (_:xs)) = List_Val xs
apply_unop Print v = trace (show v) $ List_Val []  -- ???

--
value_of_k :: Exp -> Env -> Cont -> Store -> SchedState -> (FinalAnswer, Store)

value_of_k (Const_Exp n) env cont store sched =
  apply_cont store sched cont (Num_Val n)

value_of_k (Const_List_Exp nums) env cont store sched =
  apply_cont store sched cont (List_Val (map Num_Val nums))

value_of_k (Var_Exp var) env cont store sched =
  let (loc,store') = apply_env env store var
      val = deref store' loc
  in
    apply_cont store' sched cont val

value_of_k (Diff_Exp exp1 exp2) env cont store sched =
  value_of_k exp1 env (Diff1_Cont exp2 env cont) store sched 

value_of_k (Unary_Exp op exp1) env cont store sched =
  value_of_k exp1 env (Unop_Arg_Cont op cont) store sched
  
value_of_k (If_Exp exp1 exp2 exp3) env cont store sched =
  value_of_k exp1 env (If_Test_Cont exp2 exp3 env cont) store sched

value_of_k (Let_Exp var exp1 body) env cont store sched =
  value_of_k exp1 env (Let_Exp_Cont var body env cont) store sched

value_of_k (Letrec_Exp nameArgBodyList letrec_body) env cont store sched =
  value_of_k letrec_body (extend_env_rec nameArgBodyList env) cont store sched

value_of_k (Proc_Exp var body) env cont store sched =
  apply_cont store sched cont (Proc_Val (procedure var body env))

value_of_k (Call_Exp rator rand) env cont store sched =
  value_of_k rator env (Rator_Cont rand env cont) store sched
  
value_of_k (Block_Exp [exp]) env cont store sched =
  value_of_k exp env cont store sched 

value_of_k (Block_Exp (exp:exps)) env cont store sched =
  value_of_k (Call_Exp (Proc_Exp "$dummy" (Block_Exp exps)) exp) env cont store sched

value_of_k (Set_Exp x exp) env cont store sched=
  let (loc,store') = apply_env env store x in
  value_of_k exp env (Set_Rhs_Cont loc cont) store' sched 

value_of_k (Spawn_Exp exp) env cont store sched =
  value_of_k exp env (Spawn_Cont cont) store sched

value_of_k (Yield_Exp) env cont store sched =
  let yieldsched =
        place_on_ready_queue
          (\store' sched' -> apply_cont store' sched' cont (Num_Val 99))
          sched
  in  run_next_thread store yieldsched 

value_of_k (Mutex_Exp) env cont store sched =
  let (mutex, store') = new_mutex store in
    apply_cont store' sched cont (Mutex_Val mutex)

value_of_k (Wait_Exp exp) env cont store sched =
  value_of_k exp env (Wait_Cont cont) store sched

value_of_k (Signal_Exp exp) env cont store sched =
  value_of_k exp env (Signal_Cont cont) store sched


--
value_of_program :: Exp -> Integer -> ExpVal

value_of_program exp timeslice =
  let (finalVal, _) = 
        value_of_k exp initEnv End_Main_Thread_Cont 
           initStore (initialize_scheduler timeslice)
  in finalVal


--
initEnv = empty_env

--
apply_procedure_k :: Proc -> ExpVal -> Store -> SchedState -> Cont -> (FinalAnswer, Store)
apply_procedure_k proc arg store sched cont =
  let (loc,store') = newref store arg in
   value_of_k (body proc) (extend_env (var proc) loc (saved_env proc)) cont store' sched
