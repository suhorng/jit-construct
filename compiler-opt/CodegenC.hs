module CodegenC (genC) where

import CoreExpr

genC e = concatMap ('\n':) $ pre ++ indent (genCs e) ++ post where
  pre  = [ "#include <cstdio>"
         , "#include <cstdint>"
         , ""
         , "const size_t MEM_SIZE = 1048576;"
         , "int8_t mem_arr[MEM_SIZE];"
         , "int8_t& mem(int pos) {"
         , "   return mem_arr[pos + MEM_SIZE/2];"
         , "}"
         , ""
         , "int main() {"
         , "   const int x0 = 0;"]
  post = [ "   return 0;"
         , "}"
         , ""]

indent = map ("   " ++)

genCs :: Expr -> [String]
genCs (Let x (Add y z) e) =
  concat ["const auto x", show x, " = ", genOp y, " + ", genOp z, ";"]:genCs e
genCs (Let x (Mul y z) e) =
  concat ["const auto x", show x, " = ", genOp y, " * ", genOp z, ";"]:genCs e
genCs (Load x op e) =
  concat ["const int8_t x", show x, " = mem(", genOp op, ");"]:genCs e
genCs (Store x op e) =
  concat ["mem(", genOp x, ") = ", genOp op, ";"]:genCs e
genCs (While x (x1, x2) e e') =
  concat ["int x", show x, " = x", show x1, ";"]:
  concat ["while (mem(x", show x0, ") != 0) {"]:
  (indent (genCs e) ++ update ["}"] ++ genCs e')
  where (x0, update) =
          if x1 == x2
          then (x1, id)
          else (x, (concat ["   x", show x, " = x", show x2, ";"]:))
genCs (GetChar x e) = concat ["mem(x", show x, ") = getchar();"]:genCs e
genCs (PutChar x e) = concat ["putchar(mem(x", show x, "));"]:genCs e
genCs Stop = []

genOp :: Operand -> String
genOp (Var x) = 'x':show x
genOp (Imm n)
  | n >= 0 = show n
  | otherwise = concat ["(", show n, ")"]
