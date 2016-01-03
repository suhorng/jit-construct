module Simplifier where

import CoreExpr

{- Try to use finally-tagless some day? -}

data PExpr = PVar Int
           | PImm Int
           | PAdd Int Int -- var + imm
           | PMul Int Int -- var * imm

peval :: Expr -> Expr
peval (Let x c@(Add (Var y) (Imm 0)) e) = Let x c (peval (psubst e (PVar y) x))
peval (Let x c@(Add (Var y) (Imm n)) e) = Let x c (peval (psubst e (PAdd y n) x))
peval (Let x c@(Mul (Var y) (Imm n)) e) = Let x c (peval (psubst e (PMul y n) x))
peval (Load x op e) = Load x op (peval e)
peval (Store x op e) = Store x op (peval e)
peval (While x (x1, x2) e1 e2) = doWhileXs (peval e2) where
  e1' = peval e1
  x2' = getBinding e1' x2
  doWhileXs e2'
    | x == x2'  = While x (x1, x1) (psubst e1' (PVar x1) x) (psubst e2' (PVar x1) x)
    | otherwise = While x (x1, x2') e1' e2'
  getBinding (Let y c e) x
    | y == x, Add (Var z) (Imm 0) <- c = z
    | otherwise = getBinding e x
  getBinding (Load y op e) x
    | y == x = x
    | otherwise = getBinding e x
  getBinding (Store _ _ e) x = getBinding e x
  getBinding (While y (x1, x2) e1 e2) x
    | y == x = x
    | otherwise = getBinding e2 x
  getBinding (GetChar _ e) x = getBinding e x
  getBinding (PutChar _ e) x = getBinding e x
  getBinding Stop x = x
peval (GetChar x e) = GetChar x (peval e)
peval (PutChar x e) = PutChar x (peval e)
peval Stop = Stop

{-
  get x >>= put x    = return ()            -- not implemented
  put x v >> get x   = put x v >> return v
  put x _ >> put x v = put x v

  A more general approach would be using SSA construction
  algorithm as in the `mem2reg` pass of LLVM.
-}

memeval :: Expr -> Expr
memeval (Let x c e) = Let x c (memeval e)
memeval (Load x op e) = Load x op (memeval e)
memeval (Store x op e) = doStoreX (memeval (putGet e x op)) where
  doStoreX e =
    case x of
      Var x' | putPut e x' -> e
      _ -> Store x op e

  putGet :: Expr -> Operand -> Operand -> Expr
  putGet (Let y c e) x v = Let y c (putGet e x v)
  putGet (Load y op e) x v
    | op == x, Var _ <- v = Let y (Add v (Imm 0)) (putGet e x v)
    | op == x, Imm _ <- v = Let y (Add v (Imm 0)) (putGet e x v)
    -- note: created unhandled pattern `Imm + Imm` here
  putGet (Load y op e) x v = Load y op (putGet e x v)
  putGet e@(Store _ _ _) x v = e
  putGet e@(While _ _ _ _) x v = e
  putGet e@(GetChar _ _) x v = e
  putGet (PutChar y e) x v = PutChar y (putGet e x v)
  putGet Stop x v = Stop

  {-
    putPut e x returns True only if there is another write operation
    to x before any possible load from x.

    - put/get case should have been eliminated (hence `False` in `Load`)
      Further work: Load could possible be skipped if we can prove that
      y /= x. For example, `y = z + a` while `x = z + b`

    - Another possible improvement: there is a write to x in e2 while
      no read from x in e1
  -}
  putPut :: Expr -> Int -> Bool
  putPut (Let y c e) x = putPut e x
  putPut (Load y _ _) x = False
  putPut (Store op _ e) x
    | Var y <- op, y == x = True
    | otherwise = putPut e x
  putPut (While _ _ e1 e2) x = False
  putPut (GetChar y e) x
    | y == x = True
    | otherwise = putPut e x
  putPut (PutChar _ _) x = False
  putPut Stop x = False

  injOp (Var x) = PVar x
  injOp (Imm n) = PImm n
memeval (While y xs e1 e2) = While y xs (memeval e1) (memeval e2)
memeval (GetChar x e) = GetChar x (memeval e)
memeval (PutChar x e) = PutChar x (memeval e)
memeval Stop = Stop

-- Drop unused bindings
bindeval :: Expr -> Expr
bindeval = bindeval' 0

bindeval' :: Int -> Expr -> Expr
bindeval' loopptr (Let x c e) = doLetX (bindeval' loopptr e) where
  doLetX e = if x == loopptr || bindused e x then Let x c e else e
bindeval' loopptr (Load x op e) = doLoadX (bindeval' loopptr e) where
  doLoadX e = if x == loopptr || bindused e x then Load x op e else e
bindeval' loopptr (Store x op e) = Store x op (bindeval' loopptr e)
bindeval' loopptr (While y (x1, x2) e1 e2) = While y (x1, x2) (bindeval' x2 e1) (bindeval' loopptr e2)
bindeval' loopptr (GetChar x e) = GetChar x (bindeval' loopptr e)
bindeval' loopptr (PutChar x e) = PutChar x (bindeval' loopptr e)
bindeval' loopptr Stop = Stop

bindused :: Expr -> Int -> Bool
bindused (Let y (Add op1 op2) e) x = bindInOp op1 x || bindInOp op2 x || bindused e x
bindused (Let y (Mul op1 op2) e) x = bindInOp op1 x || bindInOp op2 x || bindused e x
bindused (Load y op e) x = y == x || bindInOp op x || bindused e x
bindused (Store y op e) x = bindInOp y x || bindInOp op x || bindused e x
bindused (While y (x1, x2) e1 e2) x = x1 == x || bindused e1 x || bindused e2 x
bindused (GetChar y e) x = y == x || bindused e x
bindused (PutChar y e) x = y == x || bindused e x
bindused Stop x = False

bindInOp (Var y) x = y == x
bindInOp (Imm _) x = False

-- e1 [ e2 / x ] is written as psubst e1 e2 x
psubst :: Expr -> PExpr -> Int -> Expr
psubst (Let y (Add (Var x') (Imm n)) e1) e2@(PAdd z m) x
  | x == x' = Let y (Add (Var z) (Imm (n+m))) (psubst e1 e2 x)
psubst (Let y (Add op1 op2) e1) e2 x = Let y (Add (psubstOp op1 e2 x) (psubstOp op2 e2 x)) (psubst e1 e2 x)
psubst (Let y (Mul op1 op2) e1) e2 x = Let y (Mul (psubstOp op1 e2 x) (psubstOp op2 e2 x)) (psubst e1 e2 x)
psubst (Load y op e1) e2 x = Load y (psubstOp op e2 x) (psubst e1 e2 x)
psubst (Store y op e1) e2 x = Store (psubstOp y e2 x) (psubstOp op e2 x) (psubst e1 e2 x)
psubst (While y (x1, x2) e1 e1') e2 x = While y (x1', x2') (psubst e1 e2 x) (psubst e1' e2 x) where
  x1' = case e2 of
          PVar y | x1 == x -> y
          _ -> x1
  x2' = case e2 of
          PVar y | x2 == x -> y
          _ -> x2
psubst (GetChar y e1) e2 x
  | y == x, PVar z <- e2 = GetChar z (psubst e1 e2 x)
  | otherwise = GetChar y (psubst e1 e2 x)
psubst (PutChar y e1) e2 x
  | y == x, PVar z <- e2 = PutChar z (psubst e1 e2 x)
  | otherwise = PutChar y (psubst e1 e2 x)
psubst Stop _ _ = Stop

psubstOp (Var y) (PVar z) x | y == x = Var z
psubstOp (Var y) (PImm n) x | y == x = Imm n
psubstOp op e2 x = op
