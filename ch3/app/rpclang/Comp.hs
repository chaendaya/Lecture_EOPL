module Comp where 

import qualified Expr as R 
import qualified ActorExpr as A  

import qualified Data.Map as Map

type Identifier = String
type Location = String
type SEnv = Map.Map Identifier Identifier 
type Cont = A.Exp -> A.Exp
type Table = Map.Map Identifier ([Identifier], Identifier, A.Exp)  -- (y1,...,yk, x, e)

comp :: R.Exp -> Location -> SEnv -> Cont -> Integer -> Table -> (A.Exp, Integer, Table)
comp (R.Var_Exp x) loc senv k n tbl = 
    let y = apply_senv senv x in 
        (k (A.Var_Exp y), n, tbl)
        -- (A.Call_Exp k (A.Var_Exp y), n, tbl)
    
comp (R.Proc_Exp locb x e) loc senv k n tbl =
    let x' ="x" ++ show n
        senv' = Map.insert x x' senv
        k' = \v -> v
        fid = "f" ++ show n
        (body, n1, tbl1) = comp e locb senv' k' (n+1) tbl
        tbl2 = Map.insert fid ([], x', body) tbl1
    in (k (A.Var_Exp fid), n1, tbl2)
    
comp (R.Call_Exp e1 locb e2) loc senv k n tbl
    | locb == loc =               -- local procedure call
        let (clo, n1, tbl1) = comp e1 loc senv (\v->v) n tbl
            (arg, n2, tbl2) = comp e2 loc senv (\v->v) n1 tbl1
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
        wrap (fid, ([], x, body)) acc =
            A.Let_Exp fid (A.Proc_Exp x body) acc