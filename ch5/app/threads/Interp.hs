
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

apply_cont :: Cont -> ExpVal -> Store -> SchedState -> (FinalAnswer, Store)
apply_cont cont val store sched =
  if time_expired sched
  then
    let info = current_info sched
        sched' = place_on_ready_queue
                    (Thread info (apply_cont cont val)) 
                    sched
    in  run_next_thread store sched'
    
  else
    let sched' = decrement_timer sched
    in  apply_cont' cont val store sched'
    
  where
    apply_cont' End_Main_Thread_Cont v store sched =
      let sched' = set_final_answer sched v in 
        run_next_thread store sched'

    apply_cont' (Zero1_Cont cont) num1 store sched =
      apply_cont cont
        (if expval_num num1 == 0
         then Bool_Val True
         else Bool_Val False) store sched 

    apply_cont' (Let_Exp_Cont var body env cont) val1 store sched =
      let (loc,store') = newref store val1
      in  value_of_k body (extend_env var loc env) cont store' sched

    apply_cont' (If_Test_Cont exp2 exp3 env cont) v store sched =
      if expval_bool v
      then value_of_k exp2 env cont store sched
      else value_of_k exp3 env cont store sched

    apply_cont' (Diff1_Cont exp2 env cont) val1 store sched =
      value_of_k exp2 env (Diff2_Cont val1 cont) store sched

    apply_cont' (Diff2_Cont val1 cont) val2 store sched =
      let num1 = expval_num val1
          num2 = expval_num val2
      in  apply_cont cont (Num_Val (num1 - num2)) store sched 

    apply_cont' (Unop_Arg_Cont op cont) val store sched =
      let res = apply_unop op val in
        res `seq` apply_cont cont res store sched

    apply_cont' (Rator_Cont rand env cont) ratorVal store sched =
      value_of_k rand env (Rand_Cont ratorVal cont) store sched 

    apply_cont' (Rand_Cont ratorVal cont) randVal store sched =
      let proc = expval_proc ratorVal in
        apply_procedure_k proc randVal cont store sched

    apply_cont' (Set_Rhs_Cont loc cont) val store sched =
      let store' = setref store loc val in
        apply_cont cont (Num_Val 23) store' sched 

    apply_cont' (Spawn_Cont saved_cont) val store sched =
      let proc1 = expval_proc val
          -- fresh tid
          child_tid = the_next_tid sched
          -- parent tid
          parent_tid = tid_self (current_info sched)
          -- child thread
          child_info = 
            ThreadInfo { tid_self = child_tid,
                         tid_parent = parent_tid
                       }
          child_thread = 
            Thread { thread_info = child_info,
                     thread_fun = (apply_procedure_k 
                                      proc1 
                                      (Num_Val child_tid) 
                                      End_Subthread_Cont)
                   }
          -- enqueue child
          sched1 = sched { the_next_tid = child_tid + 1 }
          sched2 = place_on_ready_queue child_thread sched1
      in  apply_cont saved_cont (Num_Val child_tid) store sched2 

    apply_cont' (Wait_Cont saved_cont) val store sched =
      let info = current_info sched
          th = Thread info (apply_cont saved_cont (Num_Val 52))
      in wait_for_mutex (expval_mutex val) th store sched

    apply_cont' (Signal_Cont saved_cont) val store sched =
      let info = current_info sched
          th = Thread info (apply_cont saved_cont (Num_Val 53))
      in signal_mutex (expval_mutex val) th store sched

    apply_cont' (End_Subthread_Cont) val store sched =
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
  apply_cont cont (Num_Val n) store sched 

value_of_k (Const_List_Exp nums) env cont store sched =
  apply_cont cont (List_Val (map Num_Val nums)) store sched 

value_of_k (Var_Exp var) env cont store sched =
  let (loc,store') = apply_env env store var
      val = deref store' loc
  in apply_cont cont val store' sched

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
  apply_cont cont (Proc_Val (procedure var body env)) store sched 

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
  let info = current_info sched
      th = Thread info (apply_cont cont (Num_Val 99))
      yieldsched = place_on_ready_queue th sched
  in  run_next_thread store yieldsched 

value_of_k (Mutex_Exp) env cont store sched =
  let (mutex, store') = new_mutex store in
    apply_cont cont (Mutex_Val mutex) store' sched 

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
apply_procedure_k :: Proc -> ExpVal -> Cont -> Store -> SchedState -> (FinalAnswer, Store)
apply_procedure_k proc arg cont store sched =
  let (loc,store') = newref store arg in
   value_of_k (body proc) (extend_env (var proc) loc (saved_env proc)) cont store' sched
