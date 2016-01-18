{-# LANGUAGE FlexibleContexts, DeriveGeneric #-}

module CodegenX86 where

import CoreExpr

import Control.Monad.State.Strict
import Control.Monad.Writer
import Control.Monad

import Text.PrettyPrint.GenericPretty

tells xs = tell [concat xs]

genX86bf e = concat $ map (++ "\n") . execWriter . evalStateT genCode $ 0 where
  genCode = do
    tell ["global _main",
          "global _rt_getchar",
          "global _rt_putchar",
          "extern _getchar",
          "extern _putchar",

          "[section .text]",
          "_rt_getchar:",
          "  sub esp, 12",
          "  mov [esp], eax   ; save registers",
          "  mov [esp+4], ecx ; save registers",
          "  mov [esp+8], edx ; save registers",
          "  call _getchar",
          "  mov edx, [esp+16]",
          "  mov [edx], al",
          "  mov eax, [esp]",
          "  mov ecx, [esp+4]",
          "  mov edx, [esp+8]",
          "  add esp, 12",
          "  ret 4",

          "_rt_putchar:",
          "  sub esp, 16",
          "  mov [esp+4], eax  ; save registers",
          "  mov [esp+8], ecx  ; save registers",
          "  mov [esp+12], edx ; save registers",
          "  mov edx, [esp+20]",
          "  movzx eax, byte [edx]",
          "  mov [esp], eax",
          "  call _putchar",
          "  mov eax, [esp+4]",
          "  mov ecx, [esp+8]",
          "  mov edx, [esp+12]",
          "  add esp, 16",
          "  ret 4",

          "_main:",
          "  push edi",
          "  push esi",
          "  push ebx",
          "  push ebp",
          "  mov ebp, esp",
          "  sub esp, 8192",
          "  cld",
          "  xor eax, eax",
          "  mov ecx, 8192/4",
          "  mov edi, esp",
          "  rep stosd",
          "  lea esi, [esp + 4096]" ]
    --genX86bf' e
    tell ["  leave",
          "  pop ebx",
          "  pop esi",
          "  pop edi",
          "  ret"]

newLabel :: (MonadState Int m) => m String
newLabel = do
  lbl <- get
  modify (+1)
  return ("L" ++ show lbl)

genX86bf' :: (MonadState Int m, MonadWriter [String] m) => VX86Inst -> m ()
genX86bf' (MOV dst src) = tells ["  mov   ", extractOp dst, ", ", extractOp src]
genX86bf' (ADD dst src) = tells ["  add   ", extractOp dst, ", ", extractOp src]
genX86bf' (PUSH src) =    tells ["  push  ", extractOp src]
genX86bf' (POP src) =     tells ["  pop   ", extractOp src]
genX86bf' (CALL fn) =     tells ["  call  ", fn]
genX86bf' (WhileNZ ptr loop) = do
  let ptr' = case ptr of { Reg reg -> Indir reg 0; Val n -> Indir "" n }
  lbl1 <- newLabel
  lbl2 <- newLabel
  tells [lbl1, ":"]
  tells ["  cmp   ", extractOp ptr', ", ", extractOp (Val 0)]
  tells ["  jz    ", lbl2]
  mapM_ genX86bf' loop
  tells ["  jmp   ", lbl1]
  tells [lbl2, ":\n"]
genX86bf' inst = error $ "genX86bf': unrecognized instruction '" ++ show inst ++ "'"

extractOp (Reg reg) = reg
extractOp (Val n) = show n
extractOp (Indir basereg 0) = "[" ++ basereg ++ "]"
extractOp (Indir "" offset) = "[" ++ show offset ++ "]"
extractOp (Indir basereg offset) = "[" ++ basereg ++ " + " ++ show offset ++ "]"
extractOp op = error "extractOp: unsupported operand '" ++ show op ++ "'"

type VX86 = [VX86Inst]

data VX86Inst =
    MOV VX86Op VX86Op
  | ADD VX86Op VX86Op
  | PUSH VX86Op
  | POP VX86Op
  | CALL String
  | AddNew Int VX86Op VX86Op
  | Spill Int Int -- save a virtual register to memory
  | Cache VX86Op VX86Op -- cache a value in a register; hence can be discarded
  | WhileNZ VX86Op VX86 -- while the content of the register is not zero
  | Call String VX86Op
  deriving (Generic, Show)

data VX86Op = Virt Int | Arg Int | Local Int
            | Reg String  | Val Int | MemImm Int | MemVirt Int
            | Indir String Int
            deriving (Generic, Show, Eq)

instance Out VX86Inst
instance Out VX86Op

injVX86 :: Expr -> VX86
injVX86 (Let x (Add (Var y) (Imm n)) e) = AddNew x (Virt y) (Val n):injVX86 e
injVX86 e@(Let x c _) = error ("injVX86: Not implemented:\n" ++ printCode e)
injVX86 (Load x (Var y) e) = Cache (Virt x) (MemVirt y):injVX86 e
injVX86 (Load x (Imm n) e) = Cache (Virt x) (MemImm n):injVX86 e
injVX86 (Store (Var x) (Imm m) e) = MOV (MemVirt x) (Val m):injVX86 e
injVX86 (Store (Var x) (Var y) e) = MOV (MemVirt x) (Virt y):injVX86 e
injVX86 (Store (Imm n) (Imm m) e) = MOV (MemImm n) (Val m):injVX86 e
injVX86 (Store (Imm n) (Var y) e) = MOV (MemImm n) (Virt y):injVX86 e
injVX86 (While x (x1, x2) e e')
  | x1 == x2 =
      WhileNZ (Virt x1)
        (injVX86 e):
      Cache (Virt x) (Virt x1):
      injVX86 e'
  | otherwise =
      Cache (Virt x) (Virt x1):
      WhileNZ (Virt x)
        (injVX86 e ++
        [MOV (Virt x) (Virt x2)]):
      injVX86 e'
injVX86 (GetChar x e) = Call "_rt_getchar" (Virt x):injVX86 e
injVX86 (PutChar x e) = Call "_rt_putchar" (Virt x):injVX86 e
injVX86 Stop = []
