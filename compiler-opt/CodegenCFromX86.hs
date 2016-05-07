module CodegenCFromX86 where

import CodegenX86
import Data.List (nub)

getCVars = map genCOp . nub . foldrOp filterVar (++) [] where
  filterVar (Var x) | x /= 0 = (Var x:)
  filterVar _ = id

genCCode es =
  concat [ "#include <cstdio>\n"
         , "#include <cstdint>\n"
         , "\n"
         , "int8_t mem_arr[1048576];\n"
         , "int locals[1048576];\n"
         , "int8_t& mem(int pos) {\n"
         , "   return mem_arr[pos + 514288];\n"
         , "}\n"
         , "\n"
         , "int main() {\n"
         , "int x0 = 0" ++ concatMap (", " ++) (getCVars es) ++ ";\n"
         , "int eax, ebx, ecx, edx, tmp;\n"] ++
  doGenCCode es ++
  concat [ "return 0;\n"
         , "}\n"
         , "\n"]

doGenCCode [] = ""
doGenCCode (LetAdd x y z:es) = genCOp x ++ " = " ++ genCOp y ++ " + " ++ genCOp z ++ ";\n" ++ doGenCCode es
doGenCCode (Let x y:es) = genCOp x ++ " = " ++ genCOp y ++ ";\n" ++ doGenCCode es
doGenCCode (While x (x1, x2) es xs:es') | x1 /= x2 || isReg x =
  genCOp x ++ " = " ++ genCOp x1 ++ ";\n" ++
  "while (mem(" ++ genCOp x ++ ") != 0) {\n" ++
  doGenCCode es ++
  concatMap (\(op, op') -> genCOp op ++ " = " ++ genCOp op' ++ ";\n") (genFixWorld ((x,x2):xs)) ++
  "}\n" ++
  doGenCCode es'
doGenCCode (While x (x1, x2) es xs:es') | x1 == x2 =
  "while (mem(" ++ genCOp x1 ++ ") != 0) {\n" ++
  doGenCCode es ++
  concatMap (\(op, op') -> genCOp op ++ " = " ++ genCOp op' ++ ";\n") (genFixWorld xs) ++
  "}\n" ++
  doGenCCode es'
doGenCCode (GetChar x:es) = "mem(" ++ genCOp x ++ ") = getchar();\n" ++ doGenCCode es
doGenCCode (PutChar x:es) = "putchar(mem(" ++ genCOp x ++ "));\n" ++ doGenCCode es
doGenCCode (Kill src Nothing:es) = doGenCCode es
doGenCCode (Kill src (Just dst):es) = genCOp dst ++ " = " ++  genCOp src ++ ";\n" ++ genCOp src ++ " = 0xcdcdcdcd;\n" ++ doGenCCode es
doGenCCode (MOV dst src:es) = genCOp dst ++ " = " ++ genCOp src ++ ";\n" ++ doGenCCode es
doGenCCode (LOOPNZ lbl x es:es') = error "doGenCCode: LOOPNZ"

genCOp (Var n) = 'x':show n
genCOp (Imm n) = '(':(show n ++ ")")
genCOp (Reg m) = ["eax", "ebx", "ecx", "edx", "esi", "tmp"]!!m
genCOp (Local n) = "locals[" ++ show n ++ "]"
genCOp (Mem (Var n)) = "mem(x" ++ show n ++ ")"
genCOp (Mem (Reg m)) = "mem(" ++ ["eax", "ebx", "ecx", "edx", "esi", "tmp"]!!m ++ ")"
genCOp (Mem op) = error "genCOp: Mem " ++ show op
