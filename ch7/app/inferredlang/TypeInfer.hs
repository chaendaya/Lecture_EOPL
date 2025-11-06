module TypeInfer where

import Expr
import TyEnv
import Subst
import EitherState

--
typeInfer :: Exp -> IO (Either String (Type, Subst))
typeInfer exp = return (type_of_program exp )

--
otype_to_type :: OptionalType -> Either_ String Type 
otype_to_type NoType = fresh_tyvar
otype_to_type (AType ty) = _Right ty 

fresh_tyvar = 
    do newtyvar <- _fresh 
       _Right (TyVar newtyvar)

--
type_of_program :: Exp -> Either String (Type, Subst)
type_of_program exp = 
  _run (type_of exp empty_tyenv empty_subst)
     

type_of :: Exp -> TyEnv -> Subst -> Either_ String (Type, Subst)
type_of (Const_Exp n) tyenv subst = _Right (TyInt, subst)

type_of (IsZero_Exp exp1) tyenv subst =
  do (ty1, subst1) <- type_of exp1 tyenv subst
     subst2 <- unifier ty1 TyInt subst1 exp1 
     _Right (TyBool, subst2)

type_of (Diff_Exp exp1 exp2) tyenv subst =
  do (ty1, subst1) <- type_of exp1 tyenv subst 
     subst1' <- unifier ty1 TyInt subst1 exp1 
     (ty2, subst2) <- type_of exp2 tyenv subst1' 
     subst2' <- unifier ty2 TyInt subst2 exp2 
     _Right (TyInt, subst2')

type_of exp@(If_Exp exp1 exp2 exp3) tyenv subst =
  do (ty1, subst1) <- type_of exp1 tyenv subst 
     subst1' <- unifier ty1 TyBool subst1 exp1 
     (ty2, subst2) <- type_of exp2 tyenv subst1' 
     (ty3, subst3) <- type_of exp3 tyenv subst2 
     subst4 <- unifier ty2 ty3 subst3 exp 
     _Right (ty2, subst4)  

type_of (Var_Exp var) tyenv subst = 
  case apply_tyenv tyenv var of 
    Right ty -> _Right (ty, subst)
    Left errMsg -> _Left errMsg

type_of (Let_Exp var exp1 exp2) tyenv subst = 
  do (ty1, subst1) <- type_of exp1 tyenv subst 
     type_of exp2 (extend_tyenv var ty1 tyenv) subst1

type_of (Proc_Exp var optty exp1) tyenv subst = 
  do ty1 <- otype_to_type optty 
     (ty2, subst2) <- type_of exp1 (extend_tyenv var ty1 tyenv) subst 
     _Right (TyFun ty1 ty2, subst2)

type_of exp@(Call_Exp rator rand) tyenv subst =
  do (ty1, subst1) <- type_of rator tyenv subst 
     (ty2, subst2) <- type_of rand tyenv subst1 
     resTy <- fresh_tyvar
     subst3 <- unifier ty1 (TyFun ty2 resTy) subst2 exp 
     _Right (resTy, subst3)

type_of (Letrec_Exp retOptTy f x argOptTy fbody exp1) tyenv subst =
  do retTy <- otype_to_type retOptTy 
     argTy <- otype_to_type argOptTy 
     let tyenvletrec = extend_tyenv f (TyFun argTy retTy) tyenv 
     (ty1, subst1) <- type_of fbody (extend_tyenv x argTy tyenvletrec) subst
     subst2 <- unifier ty1 retTy subst1 fbody 
     type_of exp1 tyenvletrec subst2

type_of (Pair_Exp exp1 exp2) tyenv subst = 
  do (ty1, subst1) <- type_of exp1 tyenv subst
     (ty2, subst2) <- type_of exp2 tyenv subst1
     _Right (TyPair ty1 ty2, subst2)

type_of exp@(Unpair_Exp x y exp1 exp2) tyenv subst = 
  do (pairty, subst1) <- type_of exp1 tyenv subst  
     tv1 <- fresh_tyvar
     tv2 <- fresh_tyvar
     subst2 <- unifier pairty (TyPair tv1 tv2) subst1 exp 
     let tyenv' = extend_tyenv y tv2 (extend_tyenv x tv1 tyenv)
     type_of exp2 tyenv' subst2

-- 7.4.2 The Unifier

unifier :: Type -> Type -> Subst -> Exp -> Either_ String Subst 
unifier ty1' ty2' subst expr =
  let ty1 = apply_subst_to_type ty1' subst 
      ty2 = apply_subst_to_type ty2' subst 
  in
  if ty1 == ty2 then 
    _Right subst 
  else if isTyVar ty1 then
         if no_occurrence (typeVariable ty1) ty2
         then _Right (extend_subst subst (typeVariable ty1) ty2)
         else _Left ("No occurrence violation: " ++ 
                       show ty1 ++ ", " ++ show ty2 ++ 
                       "\n  in " ++ show expr)
  else if isTyVar ty2 then 
         if no_occurrence (typeVariable ty2) ty1
         then _Right (extend_subst subst (typeVariable ty2) ty1)
         else _Left ("No occurrence violation: " ++ 
                       show ty2 ++ ", " ++ show ty1 ++ 
                       "\n  in " ++ show expr)
  else if isTyFun ty1 && isTyFun ty2 then 
        do subst1 <- unifier (argType ty1) (argType ty2) subst expr 
           subst2 <- unifier (resType ty1) (resType ty2) subst1 expr 
           _Right subst2
  else if isTyPair ty1 && isTyPair ty2 then   -- unifying two pair types !! 
       do subst1 <- unifier (fstType ty1) (fstType ty2) subst expr
          subst2 <- unifier (sndType ty1) (sndType ty2) subst1 expr
          _Right subst2 
  else _Left ("Unification failure: " ++ show ty1 ++ ", " ++ show ty2 ++
              "\n  in " ++ show expr)

no_occurrence :: TypeVariable -> Type -> Bool 
no_occurrence tyvar TyInt = True 
no_occurrence tyvar TyBool = True 
no_occurrence tyvar (TyFun argTy resTy) = 
  no_occurrence tyvar argTy && no_occurrence tyvar resTy 
no_occurrence tyvar (TyVar tyvar0) = tyvar /= tyvar0 
no_occurrence tyvar (TyPair ty1 ty2) = 
  no_occurrence tyvar ty1 && no_occurrence tyvar ty2 -- Todo !!! 