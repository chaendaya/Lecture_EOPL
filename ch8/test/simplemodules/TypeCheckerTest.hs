{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module TypeCheckerTest where

import Expr(Type(..))
import Testcase

typechecker_tests :: TestSuite
typechecker_tests =
  TestSuite
   [
     -- simple applications
     TYCK "apply_proc_in_rator_pos.checked" (Just TyInt),
     RUN  "apply_proc_in_rator_pos.checked" (Just "29"),
     --
     TDTC "checker-doesnt-ignore-type-info-in-proc"
        "(proc(x : (int -> int)) -(x,1)  30)"
        Nothing,

     TYCK "apply_simple_proc.checked" (Just TyInt),
     RUN  "apply_simple_proc.checked" (Just "29"),      
     TYCK "let_to_proc_1.checked" (Just TyInt),
     RUN  "let_to_proc_1.checked" (Just "29"),

     TYCK "nested_procs_1.checked" (Just TyInt),
     RUN  "nested_procs_1.checked" (Just "-1"),
     TYCK "nested_procs_2.checked" (Just TyInt),
     RUN  "nested_procs_2.checked" (Just "2"),
      
     -- simple letrecs
     TYCK "simple_letrec_1.checked" (Just TyInt),
     RUN  "simple_letrec_1.checked" (Just "32"),
     TYCK "simple_letrec_2.checked" (Just TyInt),
     RUN  "simple_letrec_2.checked" (Just "8"),

     TYCK "simple_letrec_3.checked" (Just TyInt),
     RUN  "simple_letrec_3.checked" (Just "20"),

     --
     TDTC "double-it" "letrec int double (n : int) = if zero?(n) then 0 \
                                \ else -( (double -(n,1)), -2) \
                                \ in (double 3)"
        (Just TyInt),

     -- tests of expressions that produce procedures
     TDTC "build-a-proc-typed" "proc (x : int) -(x,1)" (Just (TyFun TyInt TyInt)),

     TDTC "build-a-proc-typed-2" "proc (x : int) zero?(-(x,1))" (Just (TyFun TyInt TyBool)),
     TDTC "bind-a-proc-typed"
        "let f = proc (x : int) -(x,1) in (f 4)"
        (Just TyInt),

     TDTC "bind-a-proc-return-proc"
        "let f = proc (x : int) -(x,1) in f"
        (Just (TyFun TyInt TyInt)),

     TDTC "type-a-ho-proc-1"
        "proc(f : (int -> bool)) (f 3)"
        (Just (TyFun (TyFun TyInt TyBool) TyBool)),

     TDTC "type-a-ho-proc-2"
        "proc(f : (bool -> bool)) (f 3)"
        Nothing,

     TDTC "apply-a-ho-proc"
        "proc (x : int) proc (f : (int -> bool)) (f x)"
        (Just (TyFun TyInt (TyFun (TyFun TyInt TyBool) TyBool))),

     TDTC "apply-a-ho-proc-2"
        "proc (x : int) proc (f : (int -> (int -> bool))) (f x)"
        (Just (TyFun TyInt (TyFun (TyFun TyInt (TyFun TyInt TyBool)) (TyFun TyInt TyBool)))),

     TDTC "apply-a-ho-proc-3"
        "proc (x : int) proc (f : (int -> (int -> bool))) (f zero?(x))"
        Nothing,

     TDTC "apply-curried-proc"
        "((proc(x : int) proc (y : int)-(x,y)  4) 3)"
        (Just TyInt),

     TDTC "apply-a-proc-2-typed"
        "(proc (x : int) -(x,1) 4)" 
        (Just TyInt),

     TDTC "apply-a-letrec" " \
             \ letrec int f(x : int) = -(x,1) \
             \ in (f 40)"
                     (Just TyInt),

     TDTC "letrec-non-shadowing"
                "(proc (x : int) \
                   \ letrec bool loop(x : bool) =(loop x) \ 
                   \  in x \
                   \ 1)"
        (Just TyInt),

     TDTC "letrec-return-fact" " \
               \ let times = proc (x : int) proc (y : int) -(x,y) \   
               \ in letrec \
               \      int fact(x : int) = if zero?(x) then 1 else ((times x) (fact -(x,1))) \
               \    in fact"
        (Just (TyFun TyInt TyInt)),

     TDTC "letrec-apply-fcn" " \
          \ let f = proc (x : int) proc (y : int) -(x,y)  \
          \ in letrec \
          \     int loop(x : int) = if zero?(x) then 1 else ((f x) (loop -(x,1))) \
          \   in (loop 4)"
        (Just TyInt),

      TYCK "modules_declare_and_ignore.simpmod" (Just TyInt),
      RUN  "modules_declare_and_ignore.simpmod" (Just "33"),

      TYCK "modules_take_one_value.simpmod" (Just TyInt),
      RUN  "modules_take_one_value.simpmod" (Just "3"),

      -- ?? : same with modules-take-one-value
      TYCK "modules_take_one_value_no_import.simpmod" (Just TyInt),
      RUN  "modules_take_one_value_no_import.simpmod" (Just "3"),

      -- Parse error: These examples are for PROCMODULES, not for SIMPLEMODULES.
      -- TYCK "modules_take_from_parameterized_module.simpmod" Nothing,
      -- RUN  "modules_take_from_parameterized_module.simpmod" Nothing,
      -- TDTC "modules-take-from-parameterized-module" "\
      --       \ module m \
      --       \     interface \
      --       \        ((m1 : []) => [u : int]) \
      --       \     body \
      --       \        module-proc (m1 : []) [u = 3] \
      --       \ from m take u"
      --    Nothing,

      TYCK "modules_check_iface_subtyping_1.simpmod" (Just TyInt),
      RUN  "modules_check_iface_subtyping_1.simpmod" (Just "3"),

      -- if the interpreter always called the typechecker, or put
      -- only declared variables in the module, this would raise an
      -- error.  Exercise: make this modification.
      TYCK "modules_take_one_value_but_interface_bad.simpmod" Nothing,
      RUN  "modules_take_one_value_but_interface_bad.simpmod" Nothing,
      
      TYCK "modules_take_bad_value.simpmod" Nothing,
      RUN  "modules_take_bad_value.simpmod" Nothing,

      TYCK "modules_two_vals.simpmod" (Just TyInt),
      RUN  "modules_two_vals.simpmod" (Just "11"),

      TYCK "modules_two_vals_bad_interface_1.simpmod" Nothing,
      RUN  "modules_two_vals_bad_interface_1.simpmod" Nothing,

      TYCK "modules_extra_vals_are_ok_1.simpmod" (Just TyInt),
      RUN  "modules_extra_vals_are_ok_1.simpmod" (Just "3"),

      TYCK "modules_extra_vals_are_ok_2.simpmod" (Just TyInt),
      RUN  "modules_extra_vals_are_ok_2.simpmod" (Just "4"),

      TYCK "modules_two_vals_bad_interface_14.simpmod" Nothing,
      RUN  "modules_two_vals_bad_interface_14.simpmod" Nothing,

      TYCK "modules_check_letstar_1.simpmod" (Just TyInt),
      RUN  "modules_check_letstar_1.simpmod" (Just "11"),

      TYCK "modules_check_letstar_2_0.simpmod" (Just TyInt),
      RUN  "modules_check_letstar_2_0.simpmod" (Just "11"),

      TYCK "modules_check_letstar_2_05.simpmod" (Just TyInt),
      RUN  "modules_check_letstar_2_05.simpmod" (Just "33"),

      TYCK "modules_check_letstar_2_1.simpmod" (Just TyInt),
      RUN  "modules_check_letstar_2_1.simpmod" (Just "11"),

      TYCK "modules_check_letstar_2_2.simpmod" Nothing,
      RUN  "modules_check_letstar_2_2.simpmod" Nothing
   ]
