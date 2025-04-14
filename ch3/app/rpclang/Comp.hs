module Comp where 

import qualified Expr as R 
import qualified ActorExpr as A  

import qualified Data.Map as Map
import Data.List (nub, (\\))
import qualified Data.Set as Set

type Identifier = String
type Location = String
type SEnv = Map.Map Identifier Identifier 
type Cont = A.Exp -> A.Exp
type Table = Map.Map Identifier ([Identifier], Identifier, A.Exp)  -- (y1,...,yk, x, e)


-- free variable 계산
freevars :: R.Exp -> Set.Set Identifier
freevars (R.Var_Exp x) = Set.singleton x
freevars (R.Const_Exp _) = Set.empty
freevars (R.Diff_Exp e1 e2) = Set.union (freevars e1) (freevars e2)
freevars (R.Let_Exp x e1 e2) = Set.union (freevars e1) (Set.delete x (freevars e2))
freevars (R.Proc_Exp _ x body) = Set.delete x (freevars body)
freevars (R.Call_Exp e1 _ e2) = Set.union (freevars e1) (freevars e2)


comp :: R.Exp -> Location -> SEnv -> Cont -> Integer -> Table -> (A.Exp, Integer, Table)
comp (R.Var_Exp x) loc senv k n tbl = 
    let y = apply_senv senv x in 
        (k (A.Var_Exp y), n, tbl)
        -- (A.Call_Exp k (A.Var_Exp y), n, tbl)
    
comp (R.Proc_Exp locb x body) loc senv k n tbl =
    let x' = "x" ++ show n
        senv' = Map.insert x x' senv
        fv = Set.toList (freevars (R.Proc_Exp locb x body)) \\ [x]
        fv' = map (apply_senv senv) fv
        fid = "f" ++ show n
        (compiledBody, n1, tbl1) = comp body locb senv' (\v -> v) (n+1) tbl
        tbl2 = Map.insert fid (fv', x', compiledBody) tbl1
    in (k (A.Var_Exp fid), n1, tbl2)
    
comp (R.Call_Exp e1 locb e2) loc senv k n tbl
      | locb == loc =
          let (clo, n1, tbl1) = comp e1 loc senv (\v -> v) n tbl
              (arg, n2, tbl2) = comp e2 loc senv (\v -> v) n1 tbl1
          in (k (A.Call_Exp clo arg), n2, tbl2)
    | otherwise =                 -- remote procedure call
        undefined

comp (R.Const_Exp v) loc senv k n tbl = 
    (k (A.Const_Exp v), n, tbl)

comp (R.Diff_Exp e1 e2) loc senv k n tbl = 
    let (v1, n1, tbl1) = comp e1 loc senv k n tbl
        (v2, n2, tbl2) = comp e2 loc senv k n1 tbl1
    in (k (A.Diff_Exp v1 v2), n2, tbl2)

comp (R.IsZero_Exp e) loc senv k n tbl = undefined
comp (R.If_Exp e1 e2 e3) loc senv k n tbl = undefined
comp (R.Let_Exp x e1 e2) loc senv k n tbl = undefined

--
apply_senv :: SEnv -> Identifier -> Identifier
apply_senv senv x = case Map.lookup x senv of
    Just y  -> y
    Nothing -> error ("unbound variable: " ++ x)

--
wrapTable :: A.Exp -> Table -> A.Exp
wrapTable body tbl =
    foldr wrap body (Map.toList tbl)
  where
    wrap (fid, (fvs, x, fbody)) acc =
        let args = fvs ++ [x]  -- 클로저 인자 + 원래 인자
            fun = foldr A.Closure_Exp fbody args
        in A.Let_Exp fid fun acc