{-# LANGUAGE FlexibleContexts, DeriveGeneric, BangPatterns #-}

module CoreExpr where

import Brainfsck

import Control.Arrow (first, second)
import Control.Monad.State.Strict
import Control.Monad.Writer
import Control.Applicative ((<$>), Applicative(..))

import Text.PrettyPrint.GenericPretty

data Prog = Let !Int !Comp !Prog
          | Load !Int !Operand !Prog
          | Store !Operand !Operand !Prog
          | While !Int (Int, Int) !Prog !Prog
          | GetChar !Int !Prog
          | PutChar !Int !Prog
          | Stop
          deriving (Generic)

data Comp = Opr !Operand
          | Add !Comp !Comp
          | Mul !Comp !Comp
          deriving (Show, Eq, Generic)

data Operand = Var !Int
             | Imm !Int
             deriving (Show, Eq, Ord, Generic)

instance Show Prog where show = printCode
instance Out Prog
instance Out Comp
instance Out Operand

printCode :: Prog -> String
printCode = printCode' "  "
printCode' tab (Let x c e) = tab ++ "let %" ++ show x ++ " = " ++ printComp c ++ "\n" ++ printCode' tab e
printCode' tab (Load x op e) = tab ++ "%" ++ show x ++ " <- ![" ++ printOp op ++ "]\n" ++ printCode' tab e
printCode' tab (Store x op e) = tab ++ "[" ++ printOp x ++ "] := " ++ printOp op ++ "\n" ++ printCode' tab e
printCode' tab (While x (x1, x2) e e') = tab ++ "While %" ++ show x ++ "=(%" ++ show x1 ++ ",%" ++ show x2 ++ "):\n" ++ printCode' ("  " ++ tab) e ++ printCode' tab e'
printCode' tab (GetChar x e) = tab ++ "GetChar [%" ++ show x ++ "]\n" ++ printCode' tab e
printCode' tab (PutChar x e) = tab ++ "PutChar [%" ++ show x ++ "]\n" ++ printCode' tab e
printCode' tab Stop = tab ++ "Stop\n"

printComp (Opr op) = printOp op
printComp (Add e1 e2) = "(" ++ printComp e1 ++ " + " ++ printComp e2 ++ ")"
printComp (Mul e1 e2) = "(" ++ printComp e1 ++ " * " ++ printComp e2 ++ ")"

printOp (Var x) = '%':show x
printOp (Imm n)
  | n < 0     = "(" ++ show n ++ ")"
  | otherwise = show n

construct :: Int -> Brainfsck -> Prog
construct ptr0 prog = evalState (construct' prog) (ptr0, ptr0 + 2)

construct' :: (Applicative m, MonadState (Int, Int) m) => Brainfsck -> m Prog
construct' []            = pure Stop
construct' (GETC:bs)     = GetChar . fst <$> get <*> construct' bs
construct' (PUTC:bs)     = PutChar . fst <$> get <*> construct' bs
construct' (LOOP bs:bs') = do
  (ptr, tmp) <- get
  modify (const (tmp, tmp+2))
  expr' <- construct' bs
  ptr' <- fst <$> get
  modify (first (const tmp))
  While tmp (ptr, ptr') expr' <$> construct' bs'
construct' (op:bs)       = do
  (ptr, tmp) <- get
  let tmp2 = tmp + 2
  modify . second $ if op == INCP || op == DECP then (+2) else (+4)
  case op of
    INCP -> Let tmp (Add (Opr (Var ptr)) (Opr (Imm 1))) <$>
            (modify (first (const tmp)) *> construct' bs)

    DECP -> Let tmp (Add (Opr (Var ptr)) (Opr (Imm (-1)))) <$>
            (modify (first (const tmp)) *> construct' bs)

    INCM -> Load tmp (Var ptr) .
            Let tmp2 (Add (Opr (Var tmp)) (Opr (Imm 1))) .
            Store (Var ptr) (Var tmp2) <$>
            construct' bs

    DECM -> Load tmp (Var ptr) .
            Let tmp2 (Add (Opr (Var tmp)) (Opr (Imm (-1)))) .
            Store (Var ptr) (Var tmp2) <$>
            construct' bs
