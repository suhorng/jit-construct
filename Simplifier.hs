{-# LANGUAGE FlexibleContexts, DeriveGeneric #-}

module Simplifier where

import Control.Arrow (first)
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

data Expr = Let String Comp Expr
          | Load String Operand Expr
          | Store String Operand Expr
          | While String String Expr Expr
          | GetChar String Expr
          | PutChar String Expr
          | Stop
          deriving (Generic)

data Comp = Add Operand Operand
          | Mul Operand Operand
          deriving (Show, Generic)

data Operand = Var String
             | Imm Int
             deriving (Show, Generic)

instance Show Expr where show = printCode
instance Out Expr
instance Out Comp
instance Out Operand

printCode = printCode' "  "
printCode' tab (Let x c e) = tab ++ "Let " ++ x ++ " = " ++ printComp c ++ "\n" ++ printCode' tab e
printCode' tab (Load x op e) = tab ++ "Load " ++ x ++ " <- [" ++ printOp op ++ "]\n" ++ printCode' tab e
printCode' tab (Store x op e) = tab ++ "Store [" ++ x ++ "] <- " ++ printOp op ++ "\n" ++ printCode' tab e
printCode' tab (While x1 x2 e e') = tab ++ "While [" ++ x1 ++ "," ++ x2 ++ "]:\n" ++ printCode' ("  " ++ tab) e ++ printCode' tab e'
printCode' tab (GetChar x e) = tab ++ "GetChar &" ++ x ++ "\n" ++ printCode' tab e
printCode' tab (PutChar x e) = tab ++ "PutChar [" ++ x ++ "]\n" ++ printCode' tab e
printCode' tab Stop = tab ++ "Stop\n"

printComp (Add e1 e2) = printOp e1 ++ " + " ++ printOp e2
printComp (Mul e1 e2) = printOp e1 ++ " * " ++ printOp e2

printOp (Var x) = x
printOp (Imm n)
  | n < 0     = "(" ++ show n ++ ")"
  | otherwise = show n

maxExpr (Let x c e)      = max (fromName x) (maxExpr e)
maxExpr (Load x op e)    = max (fromName x) (maxExpr e)
maxExpr (Store x op e)   = maxExpr e
maxExpr (While x1 x2 e1 e2) = max (maxExpr e1) (maxExpr e2)
maxExpr (GetChar op e)   = maxExpr e
maxExpr (PutChar op e)   = maxExpr e
maxExpr Stop             = 1

fromName :: String -> Int
fromName = read . dropWhile (`notElem` ['0'..'9'])

construct ptr []            = (Stop, ptr)
construct ptr (GETC:bs)     = first (GetChar ptr) (construct ptr bs)
construct ptr (PUTC:bs)     = first (PutChar ptr) (construct ptr bs)
construct ptr (LOOP bs:bs') = first (While ptr ptr' expr') (construct ptr' bs') where
  (expr', ptr') = construct ptr bs
construct ptr (op:bs)       = (expr'', ptr'') where
  expr'' = case op of
            INCP -> Let tmp (Add (Var ptr) (Imm 1)) $
                    expr'

            DECP -> Let tmp (Add (Var ptr) (Imm (-1))) $
                    expr'

            INCM -> Load tmp (Var ptr) $
                    Let tmp2 (Add (Var tmp) (Imm 1)) $
                    Store ptr (Var tmp2) $
                    expr'

            DECM -> Load tmp (Var ptr) $
                    Let tmp2 (Add (Var tmp) (Imm (-1))) $
                    Store ptr (Var tmp2) $
                    expr'
  (expr', ptr'') = construct ptr' bs
  (tmp, ptr') = if op == INCP || op == DECP
                then ('p':show fresh, tmp)
                else ('m':show fresh, ptr)
  tmp2 = 'x':show (1 + fresh)
  fresh = 1 + maxExpr expr'
