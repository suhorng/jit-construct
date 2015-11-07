{-# LANGUAGE FlexibleContexts, DeriveGeneric, BangPatterns #-}

module Simplifier where

import System.CPUTime
import System.IO

import Control.Arrow (first, second)
import Control.Monad.State.Strict
import Control.Monad.Writer
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

data Expr = Let !Int !Comp !Expr
          | Load !Int Operand !Expr
          | Store !Operand !Operand !Expr
          | While !Int (Int, Int) !Expr !Expr
          | GetChar !Int !Expr
          | PutChar !Int !Expr
          | Stop
          deriving (Generic)

data Comp = Add !Operand !Operand
          | Mul !Operand !Operand
          deriving (Show, Generic)

data Operand = Var !Int
             | Imm !Int
             deriving (Show, Eq, Generic)

instance Show Expr where show = printCode
instance Out Expr
instance Out Comp
instance Out Operand

printCode :: Expr -> String
printCode = printCode' "  "
printCode' tab (Let x c e) = tab ++ "let %" ++ show x ++ " = " ++ printComp c ++ "\n" ++ printCode' tab e
printCode' tab (Load x op e) = tab ++ "%" ++ show x ++ " <- ![" ++ printOp op ++ "]\n" ++ printCode' tab e
printCode' tab (Store x op e) = tab ++ "[" ++ printOp x ++ "] := " ++ printOp op ++ "\n" ++ printCode' tab e
printCode' tab (While x (x1, x2) e e') = tab ++ "While %" ++ show x ++ "=(%" ++ show x1 ++ ",%" ++ show x2 ++ "):\n" ++ printCode' ("  " ++ tab) e ++ printCode' tab e'
printCode' tab (GetChar x e) = tab ++ "GetChar [%" ++ show x ++ "]\n" ++ printCode' tab e
printCode' tab (PutChar x e) = tab ++ "PutChar [%" ++ show x ++ "]\n" ++ printCode' tab e
printCode' tab Stop = tab ++ "Stop\n"

printComp (Add e1 e2) = printOp e1 ++ " + " ++ printOp e2
printComp (Mul e1 e2) = printOp e1 ++ " * " ++ printOp e2

printOp (Var x) = '%':show x
printOp (Imm n)
  | n < 0     = "(" ++ show n ++ ")"
  | otherwise = show n

construct :: Int -> Brainfsck -> Expr
construct ptr0 prog = evalState (construct' prog) (ptr0, ptr0 + 2)

construct' :: (Applicative m, MonadState (Int, Int) m) => Brainfsck -> m Expr
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

data Codegen0State = C0 { nextLabel :: !Int
                        , currPtrReg :: String
                        , currPtrRegNo :: !Int
                        , varRegs :: Int -> String }

regRings = cycle ["esi", "edi", "ebx", "ecx"]

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

{-
  specialized code gen:
    pointer -> in esi, edi, ebx, ecx
    address calculation -> in edx
    value calculation -> in eax
-}

genX86bf e = concat $ map (++ "\n") . execWriter . evalStateT genCode $ initSt where
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
          "  lea " ++ regRings!!0 ++ ", [esp + 4096]" ]
    genX86bf' e
    tell ["  leave",
          "  pop ebx",
          "  pop esi",
          "  pop edi",
          "  ret"]
  initSt = C0 1 (regRings!!0) 0 cxt0
  cxt0 x = if x == 0 then regRings!!0 else error ("Unbound variable %" ++ show x)

genX86bf' :: (MonadState Codegen0State m, MonadWriter [String] m) => Expr -> m ()
genX86bf' e0@(Let x (Add (Var y) (Imm n)) e) = genWrap e $ \currSt -> do
  resReg <- case varRegs currSt y of
    "eax" -> add "eax" n >> return "eax"
    _ -> leaAdd "edx" (varRegs currSt y) n >> return "edx"
  modify $ \st -> st { varRegs = \z -> if z == x then resReg else varRegs currSt z }
genX86bf' (Load x (Var y) e) = genWrap e $ \currSt -> do
  movsxb "eax" ("[" ++ varRegs currSt y ++ "]")
  modify $ \st -> st { varRegs = \z -> if z == x then "eax" else varRegs currSt z }
genX86bf' (Store (Var x) (Var y) e) = genWrap e $ \currSt -> do
  mov ("[" ++ varRegs currSt x ++ "]") "al"
genX86bf' (While x1 (x2, x3) e1 e2) = genWrap e2 $ \currSt -> do
  let l1 = nextLabel currSt
      l2 = nextLabel currSt + 1
  modify $ \st -> st { nextLabel = nextLabel st + 2 }
  let prevPtrReg = varRegs currSt x2
      nextPtrReg = currPtrReg currSt
      ptrReg = regRings!!(currPtrRegNo currSt + 1)
  modify $ \st -> st { varRegs = \z -> if z == x1 || (x2 == x3 && z == x2) then ptrReg else varRegs currSt z }
  when (currPtrRegNo currSt >= 3) $ push ptrReg
  modify $ \st -> st { currPtrReg = ptrReg }
  modify $ \st -> st { currPtrRegNo = currPtrRegNo st + 1 }
  mov ptrReg prevPtrReg
  label l1
  movsxb "eax" ("[" ++ ptrReg ++ "]")
  test "al" "al"
  jz l2
  genX86bf' e1
  when (x2 /= x3) $ mov nextPtrReg (varRegs currSt x3)
  jmp l1
  label l2
  modify $ \st -> st { currPtrRegNo = currPtrRegNo st - 1 }
  modify $ \st -> st { varRegs = \z -> if z == x1 then nextPtrReg else varRegs currSt z }
  when (x2 /= x3) $ mov nextPtrReg ptrReg
  when (currPtrRegNo currSt >= 3) $ pop ptrReg
genX86bf' (GetChar x e) = genWrap e $ \currSt -> do
  push (varRegs currSt x)
  call "_rt_getchar"
genX86bf' (PutChar x e) = genWrap e $ \currSt -> do
  push (varRegs currSt x)
  call "_rt_putchar"
genX86bf' Stop = return ()

genWrap e f = (get >>= f) >> genX86bf' e

test_ :: String -> IO ()
test_ = (print . bindeval . peval . memeval . peval . construct 0 . parse =<<) . readFile

testTime :: String -> IO ()
testTime fn = do
  s <- readFile fn
  hPutStr stderr . show . (/ 10^12) . fromIntegral =<< getCPUTime; hPutStrLn stderr " parse"
  let bfp = parse s
  hPutStr stderr . show . (/ 10^12) . fromIntegral =<< getCPUTime; hPutStrLn stderr (" construct; input length " ++ show (length bfp))
  let !ir = construct 0 bfp
  hPutStr stderr . show . (/ 10^12) . fromIntegral =<< getCPUTime; hPutStrLn stderr " peval"
  let !ir' = peval ir
  hPutStr stderr . show . (/ 10^12) . fromIntegral =<< getCPUTime; hPutStrLn stderr " memeval"
  let !ir'' = memeval ir'
  hPutStr stderr . show . (/ 10^12) . fromIntegral =<< getCPUTime; hPutStrLn stderr " peval"
  let !ir''' = peval ir''
  hPutStr stderr . show . (/ 10^12) . fromIntegral =<< getCPUTime; hPutStrLn stderr " bindeval"
  let !ir'''' = bindeval ir'''
  hPutStr stderr . show . (/ 10^12) . fromIntegral =<< getCPUTime; hPutStrLn stderr " done"
  --print ir''''
  putStr $ genX86bf ir''''
