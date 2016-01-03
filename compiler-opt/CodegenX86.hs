{-# LANGUAGE FlexibleContexts, DeriveGeneric #-}

module CodegenX86 where

import CoreExpr

import Control.Monad.State.Strict
import Control.Monad.Writer

import Text.PrettyPrint.GenericPretty

label  lbl   = tell ["L" ++ show lbl ++ ":"]
add    a   n = tell ["  add " ++ a ++ ", (" ++ show n ++ ")"]
call   lbl   = tell ["  call " ++ lbl]
jmp    lbl   = tell ["  jmp L" ++ show lbl]
jz     lbl   = tell ["  jz L" ++ show lbl]
leaAdd a b n = tell ["  lea " ++ a ++ ", [" ++ b ++ "+(" ++ show n ++ ")]"]
mov    a b   = when (a /= b) $ tell ["  mov " ++ a ++ ", " ++ b]
movsxb a b   = tell ["  movsx " ++ a ++ ", byte " ++ b]
push   a     = tell ["  push " ++ a]
pop    a     = tell ["  pop " ++ a]
test   a b   = tell ["  test " ++ a ++ ", " ++ b]
ref    x     = "[" ++ x ++ "]"

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
    genX86bf' e
    tell ["  leave",
          "  pop ebx",
          "  pop esi",
          "  pop edi",
          "  ret"]

genX86bf' :: (MonadState s m, MonadWriter [String] m) => Expr -> m ()
genX86bf' = undefined

type VX86 = [VX86Inst]

data VX86Inst =
    MOV VX86Op VX86Op
  | ADD VX86Op VX86Op
  | LEA VX86Op VX86Op
  | PUSH VX86Op
  | POP VX86Op
  | CALL String
  | AddNew Int VX86Op VX86Op
  | Spill Int Int -- save a virtual register to memory
  | Cache String VX86Op -- cache a value in a register; hence can be discarded
  | WhileNZ String VX86 -- while the content of the register is not zero
  | Call VX86Op
  deriving (Generic, Show)

data VX86Op = Virt Int | ArgO Int | ArgI Int | Local Int
            | Reg String  | Val Int
            deriving (Generic, Show)

instance Out VX86Inst
instance Out VX86Op

injVX86 :: Expr -> VX86
injVX86 = undefined
