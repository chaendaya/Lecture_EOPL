{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module Actors.Expr(Program,Exp(..),Identifier,UnaryOp(..)) where

type Program = Exp
  
data Exp =
    Const_Exp  Int
  | Diff_Exp   Exp Exp
  | If_Exp     Exp Exp Exp
  | Var_Exp    Identifier                 -- variable : x
  | Let_Exp    Identifier Exp Exp         -- let x = expression in expression
  | Letrec_Exp
      [(Identifier,Identifier,Exp)] Exp   -- letrec { ..., f_i(x_i) = expression_i, ... } in expression
  | Proc_Exp   Identifier Exp             -- proc ( identifier ) expression
  | Call_Exp   Exp Exp                    -- ( expression expression)
  | Block_Exp  [ Exp ]                    -- begin exp1; ...; expk end
  | Set_Exp    Identifier Exp             -- set x = expression
  | Spawn_Exp  Exp                        -- spawn ( expression )
  | Yield_Exp                             -- yield ()
  | Mutex_Exp                             -- mutex ()
  | Wait_Exp  Exp                         -- wait ( expression )
  | Signal_Exp  Exp                       -- signal ( expression )
  | Const_List_Exp   [Int]                -- number list : [ number1, ..., numberk ]
  | Unary_Exp  UnaryOp Exp                -- unop ( expression ) where unop is one of car, cdr, null?, zero? print
  -- | Try_Exp    Exp Identifier Exp         -- try exp catch exn exp
  -- | Raise_Exp  Exp                        -- raise exp

  -- For Actors
  | Send_Exp [ Exp ]                      -- send ( to , msgs ) -> send ( SendExpressionList )
  | Ready_Exp Exp                         -- ready ( expression ) 
  | New_Exp   Exp                         -- new ( expression )
  | Eq_Actor_Exp Exp Exp                  -- actor? ( actor, actor )

  -- For Tuple
  | Tuple_Exp [ Exp ]                     -- ( expression1, ..., expressionk )
  | LetTuple_Exp [ Identifier ] Exp Exp   -- let x1, ..., xk = expression in expression
  
  deriving Show

data UnaryOp = IsZero | IsNull | Car | Cdr | Print deriving Show

type Identifier = String

pprint :: Exp -> String
pprint = undefined