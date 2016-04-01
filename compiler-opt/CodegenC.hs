module CodegenC (genC) where

import CoreExpr

genC e = concatMap ('\n':) $ pre ++ indent (genCs e) ++ post where
  pre = [ "#include <cstdio>"
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
genCs (Let x (Mul y z) e) = undefined
  concat ["const auto x", show x, " = ", genOp y, " * ", genOp z, ";"]:genCs e
genCs (Load x y e) =
  concat ["const int8_t x", show x, " = mem(", genOp y, ");"]:genCs e
genCs (Store x y e) =
  concat ["mem(", genOp x, ") = ", genOp y, ";"]:genCs e
genCs (While x1 (x2, x3) e e') =
  concat ["int x", show x1, " = x", show x2, ";"]:
  concat ["while (mem(x", show x1, ") != 0) {"]:
  (indent (genCs e) ++
   (if x2 == x3
    then ["}"]
    else [concat ["   x", show x1, " = x", show x3, ";"],
          "}"]) ++
   genCs e')
genCs (GetChar x e) = concat ["mem(x", show x, ") = getchar();"]:genCs e
genCs (PutChar x e) = concat ["putchar(mem(x", show x, "));"]:genCs e
genCs Stop = []

genOp :: Operand -> String
genOp (Var x) = 'x':show x
genOp (Imm n)
  | n >= 0 = show n
  | otherwise = concat ["(", show n, ")"]
