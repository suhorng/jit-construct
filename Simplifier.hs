{-# LANGUAGE FlexibleContexts, DeriveGeneric #-}

module Simplifier where

import Control.Arrow (first, second)
import Control.Monad.State
import Control.Applicative ((<$>), Applicative(..))
import Data.Char (chr, ord)
import Data.Word

import Text.PrettyPrint.GenericPretty

data BrainfsckOp = INCP | DECP | INCM | DECM | GETC | PUTC | LOOP Brainfsck
                 deriving (Show, Eq)
type Brainfsck   = [BrainfsckOp]

parse :: String -> Brainfsck
parse = parse' [id] where
  parse' [f]       []       = f []
  parse' (f:fs)    ('>':ss) = parse' ((f . (INCP:)) : fs) ss
  parse' (f:fs)    ('<':ss) = parse' ((f . (DECP:)) : fs) ss
  parse' (f:fs)    ('+':ss) = parse' ((f . (INCM:)) : fs) ss
  parse' (f:fs)    ('-':ss) = parse' ((f . (DECM:)) : fs) ss
  parse' (f:fs)    ('.':ss) = parse' ((f . (PUTC:)) : fs) ss
  parse' (f:fs)    (',':ss) = parse' ((f . (GETC:)) : fs) ss
  parse' fs        ('[':ss) = parse' (id:fs) ss
  parse' (f:f':fs) (']':ss) = parse' ((f' . (LOOP (f []):)) : fs) ss
  parse' fs        (_:ss)   = parse' fs ss

type Mem = [Word8]

new    n          = replicate n 0
deref  mem addr   = mem!!addr
update mem addr x = prefix ++ (x:suffix) where
  (prefix, _:suffix) = splitAt addr mem
mmodify mem addr f = update mem addr (f (deref mem addr))

interp :: Int -> Brainfsck -> String -> String
interp n = interp' (new n) 0 where
  ord' = fromIntegral . ord
  chr' = chr . fromIntegral

  interp' :: [Word8] -> Int -> Brainfsck -> String -> String
  interp' mem ptr []        inp      = []
  interp' mem ptr (INCP:bs) inp      = interp' mem (ptr+1) bs inp
  interp' mem ptr (DECP:bs) inp      = interp' mem (ptr-1) bs inp
  interp' mem ptr (INCM:bs) inp      = interp' (mmodify mem ptr (+1)) ptr bs inp
  interp' mem ptr (DECM:bs) inp      = interp' (mmodify mem ptr (subtract 1)) ptr bs inp
  interp' mem ptr (GETC:bs) (ch:inp) = interp' (update mem ptr (ord' ch)) ptr bs inp
  interp' mem ptr (PUTC:bs) inp      = chr' (deref mem ptr) : interp' mem ptr bs inp
  interp' mem ptr bs@(LOOP loop:rest) inp =
    if deref mem ptr /= 0
    then interp' mem ptr (loop ++ bs) inp
    else interp' mem ptr rest inp

data Expr = Let Int Comp Expr
          | Load Int Operand Expr
          | Store Operand Operand Expr
          | While Int Int Expr Expr
          | GetChar Int Expr
          | PutChar Int Expr
          | Stop
          deriving (Generic)

data Comp = Add Operand Operand
          | Mul Operand Operand
          deriving (Show, Generic)

data Operand = Var Int
             | Imm Int
             deriving (Show, Eq, Generic)

instance Show Expr where show = printCode
instance Out Expr
instance Out Comp
instance Out Operand

printCode :: Expr -> String
printCode = printCode' "  "
printCode' tab (Let x c e) = tab ++ "Let %" ++ show x ++ " = " ++ printComp c ++ "\n" ++ printCode' tab e
printCode' tab (Load x op e) = tab ++ "Load %" ++ show x ++ " <- [" ++ printOp op ++ "]\n" ++ printCode' tab e
printCode' tab (Store x op e) = tab ++ "Store [" ++ printOp x ++ "] <- " ++ printOp op ++ "\n" ++ printCode' tab e
printCode' tab (While x1 x2 e e') = tab ++ "While [%" ++ show x1 ++ ",%" ++ show x2 ++ "]:\n" ++ printCode' ("  " ++ tab) e ++ printCode' tab e'
printCode' tab (GetChar x e) = tab ++ "GetChar [%" ++ show x ++ "]\n" ++ printCode' tab e
printCode' tab (PutChar x e) = tab ++ "PutChar [%" ++ show x ++ "]\n" ++ printCode' tab e
printCode' tab Stop = tab ++ "Stop\n"

printComp (Add e1 e2) = printOp e1 ++ " + " ++ printOp e2
printComp (Mul e1 e2) = printOp e1 ++ " * " ++ printOp e2

printOp (Var x) = '%':show x
printOp (Imm n)
  | n < 0     = "(" ++ show n ++ ")"
  | otherwise = show n

maxExpr :: Expr -> Int
maxExpr (Let x c e)      = max x (maxExpr e)
maxExpr (Load x op e)    = max x (maxExpr e)
maxExpr (Store x op e)   = maxExpr e
maxExpr (While x1 x2 e1 e2) = max (maxExpr e1) (maxExpr e2)
maxExpr (GetChar op e)   = maxExpr e
maxExpr (PutChar op e)   = maxExpr e
maxExpr Stop             = 1

maxOp :: Operand -> Int
maxOp (Var x) = x
maxOp (Imm _) = minBound

construct :: Int -> Brainfsck -> Expr
construct ptr0 prog = evalState (construct' prog) (ptr0, ptr0 + 2)

construct' :: (Applicative m, MonadState (Int, Int) m) => Brainfsck -> m Expr
construct' []            = pure Stop
construct' (GETC:bs)     = GetChar . fst <$> get <*> construct' bs
construct' (PUTC:bs)     = PutChar . fst <$> get <*> construct' bs
construct' (LOOP bs:bs') = do
  ptr <- fst <$> get
  expr' <- construct' bs
  While ptr . fst <$> get <*> pure expr' <*> construct' bs'
construct' (op:bs)       = do
  (ptr, tmp) <- get
  let tmp2 = tmp + 2
  modify . second $ if op == INCP || op == DECP then (+2) else (+4)
  case op of
    INCP -> Let tmp (Add (Var ptr) (Imm 1)) <$>
            (modify (first (const tmp)) *> construct' bs)

    DECP -> Let tmp (Add (Var ptr) (Imm (-1))) <$>
            (modify (first (const tmp)) *> construct' bs)

    INCM -> Load tmp (Var ptr) .
            Let tmp2 (Add (Var tmp) (Imm 1)) .
            Store (Var ptr) (Var tmp2) <$>
            construct' bs

    DECM -> Load tmp (Var ptr) .
            Let tmp2 (Add (Var tmp) (Imm (-1))) .
            Store (Var ptr) (Var tmp2) <$>
            construct' bs

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
peval (While x1 x2 e1 e2) = While x1 x2' e1' (psubst (peval e2) (PVar x2') x2) where
  e1' = peval e1
  x2' = getBinding e1' x2
  getBinding (Let y c e) x
    | y == x, Add (Var z) (Imm 0) <- c = z
    | otherwise = getBinding e x
  getBinding (Load y op e) x
    | y == x = x
    | otherwise = getBinding e x
  getBinding (Store _ _ e) x = getBinding e x
  getBinding (While x1 x2 e1 e2) x
    | x2 == x = x
    | otherwise = getBinding e2 x
  getBinding (GetChar y e) x
    | y == x = x
    | otherwise = getBinding e x
  getBinding (PutChar _ e) x = getBinding e x
  getBinding Stop x = x
peval (GetChar x e) = GetChar x (peval e)
peval (PutChar x e) = PutChar x (peval e)
peval Stop = Stop

-- e1 [ e2 / x ] is written as psubst e1 e2 x
psubst :: Expr -> PExpr -> Int -> Expr
psubst (Let y (Add (Var x') (Imm n)) e1) e2@(PAdd z m) x
  | x == x' = Let y (Add (Var z) (Imm (n+m))) (psubst e1 e2 x)
psubst (Let y (Add op1 op2) e1) e2 x = Let y (Add (psubstOp op1 e2 x) (psubstOp op2 e2 x)) (psubst e1 e2 x)
psubst (Let y (Mul op1 op2) e1) e2 x = Let y (Mul (psubstOp op1 e2 x) (psubstOp op2 e2 x)) (psubst e1 e2 x)
psubst (Load y op e1) e2 x = Load y (psubstOp op e2 x) (psubst e1 e2 x)
psubst (Store y op e1) e2 x = Store (psubstOp y e2 x) (psubstOp op e2 x) (psubst e1 e2 x)
psubst (While x1 x2 e1 e1') e2 x = While x1' x2 (psubst e1 e2 x) (psubst e1' e2 x) where
  x1' = case e2 of
          PVar y | x1 == x -> y
          _ -> x1
psubst (GetChar y e1) e2 x = GetChar y (psubst e1 e2 x)
psubst (PutChar y e1) e2 x = PutChar y (psubst e1 e2 x)
psubst Stop _ _ = Stop

psubstOp (Var y) (PVar z) x | y == x = Var z
psubstOp (Var y) (PImm n) x | y == x = Imm n
psubstOp op e2 x = op

test :: String -> IO ()
test = (print . peval . construct 0 . parse =<<) . readFile
