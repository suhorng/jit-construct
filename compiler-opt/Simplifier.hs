module Simplifier where

import Control.Monad (guard, mapM)
import Data.List ((\\), sort)

import Text.PrettyPrint.GenericPretty
import CoreExpr

{- Try to use finally-tagless some day? -}

peval :: Prog -> Prog
peval (Let x c e) = Let x c' (peval (psubst e c' x)) where
  c' = nomialComp (normalize c)
peval (Load x op e) = Load x op (peval e)
peval (Store x op e) = Store x op (peval e)
peval (While x (x1, x2) e1 e2) = doWhileXs (peval e2) where
  e1' = peval e1
  x2' = getBinding e1' x2
  doWhileXs e2'
    | x == x2'  = While x (x1, x1) (psubst e1' (Opr (Var x1)) x) (psubst e2' (Opr (Var x1)) x)
    | otherwise = While x (x1, x2') e1' e2'
  getBinding (Let y c e) x
    | y == x, Opr (Var z) <- c = z
    | otherwise = getBinding e x
  getBinding (Load y op e) x
    | y == x = x
    | otherwise = getBinding e x
  getBinding (Store _ _ e) x = getBinding e x
  getBinding (While y (x1, x2) e1 e2) x
    | y == x = if x1 == x2 then x1 else x
    | otherwise = getBinding e2 x
  getBinding (GetChar _ e) x = getBinding e x
  getBinding (PutChar _ e) x = getBinding e x
  getBinding Stop x = x
peval (GetChar x e) = GetChar x (peval e)
peval (PutChar x e) = PutChar x (peval e)
peval Stop = Stop

data PComp = PNomial [([Operand], Int)] !Int deriving (Show)

nomialAdd (PNomial xs1 m1) (PNomial xs2 m2) = PNomial (add xs1 xs2) (m1+m2) where
  add xs [] = xs
  add [] ys = ys
  add (x@(ps,a):xs) (y@(qs,b):ys)
    | ps < qs = x:add xs (y:ys)
    | ps > qs = y:add (x:xs) ys
    | a+b == 0 = add xs ys -- ps == qs
    | otherwise = (ps,a+b):add xs ys -- p == qs

normalize (Opr x@(Var _)) = PNomial [([x], 1)] 0
normalize (Opr (Imm m)) = PNomial [] m
normalize (Add c1 c2) = nomialAdd (normalize c1) (normalize c2)
normalize (Mul c1 c2) = foldr nomialAdd zero $ do
  (x1,c1) <- ([],m1):xs1
  (x2,c2) <- ([],m2):xs2
  case (x1 ++ x2, c1*c2) of
    (_, 0) -> []
    ([], c) -> return $ PNomial [] (c1*c2)
    (xs, c) -> return $ PNomial [(sort (x1 ++ x2), c1*c2)] 0
 where
  zero = PNomial [] 0
  PNomial xs1 m1 = normalize c1
  PNomial xs2 m2 = normalize c2

nomialComp (PNomial [] m) = Opr (Imm m)
nomialComp (PNomial xs m)
  | m == 0 = c
  | otherwise = Add (Opr (Imm m)) c
  where c = foldr1 Add . concatMap termComp $ xs
        termComp (ps, 0) = []
        termComp (ps, 1) = [foldr1 Mul (map Opr ps)]
        termComp (ps, m) = [Mul (Opr (Imm m)) (foldr1 Mul (map Opr ps))]

{-
  get x >>= put x    = return ()            -- not implemented
  put x v >> get x   = put x v >> return v
  put x _ >> put x v = put x v

  A more general approach would be using SSA construction
  algorithm as in the `mem2reg` pass of LLVM.
-}

memeval :: Prog -> Prog
memeval (Let x c e) = Let x c (memeval e)
memeval (Load x op e) = Load x op (memeval e)
memeval (Store x op e) = doStoreX (memeval (putGet e x op)) where
  doStoreX e =
    case x of
      Var x' | putPut e x' -> e
      _ -> Store x op e

  putGet :: Prog -> Operand -> Operand -> Prog
  putGet (Let y c e) x v = Let y c (putGet e x v)
  putGet (Load y op e) x v
    | op == x = Let y (Opr v) (putGet e x v)
    | otherwise = Load y op (putGet e x v)
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
  putPut :: Prog -> Int -> Bool
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
memeval (While y xs e1 e2) = While y xs (memeval e1) (memeval e2)
memeval (GetChar x e) = GetChar x (memeval e)
memeval (PutChar x e) = PutChar x (memeval e)
memeval Stop = Stop

-- Drop unused bindings
bindeval :: Prog -> Prog
bindeval = bindeval' 0

bindeval' :: Int -> Prog -> Prog
bindeval' loopptr (Let x c e) = doLetX (bindeval' loopptr e) where
  doLetX e = if x == loopptr || bindused e x then Let x c e else e
bindeval' loopptr (Load x op e) = doLoadX (bindeval' loopptr e) where
  doLoadX e = if x == loopptr || bindused e x then Load x op e else e
bindeval' loopptr (Store x op e) = Store x op (bindeval' loopptr e)
bindeval' loopptr (While y (x1, x2) e1 e2) = While y (x1, x2) (bindeval' x2 e1) (bindeval' loopptr e2)
bindeval' loopptr (GetChar x e) = GetChar x (bindeval' loopptr e)
bindeval' loopptr (PutChar x e) = PutChar x (bindeval' loopptr e)
bindeval' loopptr Stop = Stop

bindused :: Prog -> Int -> Bool
bindused (Let y c e) x = bindInComp c x || bindused e x
bindused (Load y op e) x = y == x || bindInOp op x || bindused e x
bindused (Store y op e) x = bindInOp y x || bindInOp op x || bindused e x
bindused (While y (x1, x2) e1 e2) x = x1 == x || bindused e1 x || bindused e2 x
bindused (GetChar y e) x = y == x || bindused e x
bindused (PutChar y e) x = y == x || bindused e x
bindused Stop x = False

bindInComp (Opr op) x = bindInOp op x
bindInComp (Add c1 c2) x = bindInComp c1 x || bindInComp c2 x
bindInComp (Mul c1 c2) x = bindInComp c1 x || bindInComp c2 x

bindInOp (Var y) x = y == x
bindInOp (Imm _) x = False

trivloop (Let x c e) = Let x c (trivloop e)
trivloop (Load x op e) = Load x op (trivloop e)
trivloop (Store x op e) = Store x op (trivloop e)
trivloop (While x (x1, x2) e1 e2) = trySimplify $ do
  guard (x1 == x2)
  acts <- simpleActs [] e1'
  upd@(Nothing, x, y, c) <- lookup (Opr (Var x1)) acts
  times <- case c of
    Add (Opr (Var _)) (Opr (Imm (-1))) -> return (Opr (Var x))
    Add (Opr (Imm (-1))) (Opr (Var _)) -> return (Opr (Var x))
    _ -> Nothing -- can also handle *x += 1 in addition to *x -= 1
  let acts' = filter (/= (Opr (Var x1), upd)) acts
  comps <- mapM (makeComp times) acts'
  return $ Load x (Var x1) . foldr (.) id comps . Store (Var x1) (Imm 0)
 where
  makeComp times (Opr op, (Nothing, x, y, c')) = do
    c'' <- case c' of
      Add (Opr (Var x')) c'' | x == x' -> Just c''
      Add c'' (Opr (Var x')) | x == x' -> Just c''
      _ -> Nothing
    return $
      Load x op .
      Let y (Add (Opr (Var x)) (Mul times c'')) .
      Store op (Var y)
  makeComp times (c, (Just op, x, y, c')) = do
    c'' <- case c' of
      Add (Opr (Var x')) c'' | x == x' -> Just c''
      Add c'' (Opr (Var x')) | x == x' -> Just c''
      _ -> Nothing
    return $
      Let op c .
      Load x (Var op) .
      Let y (Add (Opr (Var x)) (Mul times c'')) .
      Store (Var op) (Var y)
  makeComp _ _ = Nothing
  trySimplify (Just simp) = simp e2'
  trySimplify Nothing = While x (x1, x2) e1' e2'
  e1' = trivloop e1
  e2' = trivloop e2
trivloop (GetChar x e) = GetChar x (trivloop e)
trivloop (PutChar x e) = PutChar x (trivloop e)
trivloop Stop = Stop

compVars (Opr x@(Var _)) = [x]
compVars (Opr n@(Imm _)) = []
compVars (Add c1 c2) = compVars c1 ++ compVars c2
compVars (Mul c1 c2) = compVars c1 ++ compVars c2

simpleActs vars
  (Load x op'
  (Let y c'
  (Store op'' y' e)))
  | op' == op'', Var y == y',
    op' `notElem` vars,
    all (`notElem` vars) (compVars c') =
      fmap ((Opr op', (Nothing, x, y, c')):) (simpleActs (Var x:Var y:vars) e)
simpleActs vars
  (Let op c
  (Load x op'
  (Let y c'
  (Store op'' y' e))))
  | Var op == op', op' == op'', Var y == y',
    all (`notElem` vars) (compVars c),
    all (`notElem` vars) (compVars c') =
      fmap ((c, (Just op, x, y, c')):) (simpleActs (Var x:Var y:vars) e)
simpleActs vars Stop = Just []
simpleActs vars _ = Nothing

commons (Let x c e) = Let x c (commons (csubst e (Var x) c))
commons (Load x op e) = Load x op (commons e)
commons (Store x op e) = Store x op (commons e)
commons (While x (x1, x2) e1 e2) = While x (x1, x2) (commons e1) (commons e2)
commons (GetChar x e) = GetChar x (commons e)
commons (PutChar x e) = PutChar x (commons e)
commons Stop = Stop

csubst (Let y c' e) x c
  | c == c' = Let y c' (csubst (psubst e (Opr x) y) x c)
  | otherwise = Let y c' (csubst e x c)
csubst (Load y op e) x c = Load y op (csubst e x c)
csubst (Store y op e) x c = Store y op (csubst e x c)
csubst (While y (x1, x2) e1 e2) x c = While y (x1, x2) (csubst e1 x c) (csubst e2 x c)
csubst (GetChar y e) x c = GetChar y (csubst e x c)
csubst (PutChar y e) x c = PutChar y (csubst e x c)
csubst Stop x c = Stop

-- e1 [ e2 / x ] is written as psubst e1 e2 x
psubst :: Prog -> Comp -> Int -> Prog
psubst (Let y c e1) e2 x = Let y (psubstComp c e2 x) (psubst e1 e2 x)
psubst (Load y op e1) e2 x = Load y (psubstOp op e2 x) (psubst e1 e2 x)
psubst (Store y op e1) e2 x = Store (psubstOp y e2 x) (psubstOp op e2 x) (psubst e1 e2 x)
psubst (While y (x1, x2) e1 e1') e2 x = While y (x1', x2') (psubst e1 e2 x) (psubst e1' e2 x) where
  x1' = case e2 of
          Opr (Var y) | x1 == x -> y
          _ -> x1
  x2' = case e2 of
          Opr (Var y) | x2 == x -> y
          _ -> x2
psubst (GetChar y e1) e2 x
  | y == x, Opr (Var z) <- e2 = GetChar z (psubst e1 e2 x)
  | otherwise = GetChar y (psubst e1 e2 x)
psubst (PutChar y e1) e2 x
  | y == x, Opr (Var z) <- e2 = PutChar z (psubst e1 e2 x)
  | otherwise = PutChar y (psubst e1 e2 x)
psubst Stop _ _ = Stop

psubstComp :: Comp -> Comp -> Int -> Comp
psubstComp (Opr op) e2 x
  | Var y <- op, y == x = e2
  | otherwise = Opr op
psubstComp (Add c1 c2) e2 x = Add (psubstComp c1 e2 x) (psubstComp c2 e2 x)
psubstComp (Mul c1 c2) e2 x = Mul (psubstComp c1 e2 x) (psubstComp c2 e2 x)

psubstOp :: Operand -> Comp -> Int -> Operand
psubstOp (Var y) (Opr (Var z)) x | y == x = Var z
psubstOp (Var y) (Opr (Imm n)) x | y == x = Imm n
psubstOp op e2 x = op
