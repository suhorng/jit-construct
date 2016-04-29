{-# LANGUAGE FlexibleContexts, DeriveGeneric #-}

module CodegenX86 where

import qualified CoreExpr as E

import Control.Arrow (first, second, (&&&))
import Control.Monad
import Control.Monad.Writer.Strict
import Control.Monad.State.Strict
import Data.List (nub, (\\))
import Text.PrettyPrint.GenericPretty

{-
fn [] = undefined
fn (LetAdd x y z:es) = undefined
fn (Let x y:es) = undefined
fn (While x (x1, x2) es:es') = undefined
fn (GetChar x:es) = undefined
fn (PutChar x:es) = undefined
fn (Kill src dst:es) = undefined
fn (MOV dst src:es) = undefined
fn (LOOPNZ x es:es') = undefined
-}
type VX86 = [VX86Inst]

foldrOp f g e [] = e
foldrOp f g e (LetAdd x y z:es) = f x (f y (f z (foldrOp f g e es)))
foldrOp f g e (Let x y:es) = f x (f y (foldrOp f g e es))
foldrOp f g e (While x (x1, x2) es:es') = f x (f x1 (f x2 (g (foldrOp f g e es) (foldrOp f g e es'))))
foldrOp f g e (GetChar x:es) = f x (foldrOp f g e es)
foldrOp f g e (PutChar x:es) = f x (foldrOp f g e es)
foldrOp f g e (Kill src Nothing:es) = f src (foldrOp f g e es)
foldrOp f g e (Kill src (Just dst):es) = f src (f dst (foldrOp f g e es))
foldrOp f g e (MOV dst src:es) = f dst (f src (foldrOp f g e es))
foldrOp f g e (LOOPNZ x es:es') = f x (g (foldrOp f g e es) (foldrOp f g e es'))

data VX86Inst =
    LetAdd VX86Op VX86Op VX86Op
  | Let VX86Op VX86Op
  | While VX86Op (VX86Op, VX86Op) VX86
  | GetChar VX86Op
  | PutChar VX86Op
  | Kill VX86Op (Maybe VX86Op)
  | MOV VX86Op VX86Op
  | LOOPNZ VX86Op VX86
  deriving (Show, Generic)

data VX86Op =
    Var Int
  | Imm Int
  | Reg Int
  | Local Int
  | Mem VX86Op
  deriving (Eq, Show, Generic)

instance Out VX86Inst
instance Out VX86Op

injVX86 :: E.Expr -> VX86
injVX86 (E.Let x (E.Add y z) e) = LetAdd (Var x) (injOp y) (injOp z):injVX86 e
injVX86 (E.Let x (E.Mul y z) e) = error "injVX86: Let Mul"
injVX86 (E.Load x op e) = Let (Var x) (Mem (injOp op)):injVX86 e
injVX86 (E.Store x op e) = MOV (Mem (injOp x)) (injOp op):injVX86 e
injVX86 (E.While x (x1, x2) e e') =
  if x1 == x2 && (use x es || use x es') then error ("injVX86: While: use of " ++ show x) else
  While (Var x) (Var x1, Var x2) es:
  es'
  where use x = let x' = Var x in
                foldrOp (\op b -> b || op == x' || op == Mem x') (||) False
        es = injVX86 e
        es' = injVX86 e'
injVX86 (E.GetChar x e) = GetChar (Var x):injVX86 e
injVX86 (E.PutChar x e) = PutChar (Var x):injVX86 e
injVX86 E.Stop = []

injOp :: E.Operand -> VX86Op
injOp (E.Var x) = Var x
injOp (E.Imm n) = Imm n

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
         , "int x0 = 0" ++ concatMap (", " ++) (getCVars es) ++ ";\n"] ++
  doGenCCode es ++
  concat [ "return 0;\n"
         , "}\n"
         , "\n"]

doGenCCode [] = ""
doGenCCode (LetAdd x y z:es) = genCOp x ++ " = " ++ genCOp y ++ " + " ++ genCOp z ++ ";\n" ++ doGenCCode es
doGenCCode (Let x y:es) = genCOp x ++ " = " ++ genCOp y ++ ";\n" ++ doGenCCode es
doGenCCode (While x (x1, x2) es:es') | x1 == x2 =
  "while (mem(" ++ genCOp x1 ++ ") != 0) {\n" ++
  doGenCCode es ++
  "}\n" ++
  doGenCCode es'
doGenCCode (While x (x1, x2) es:es') | x1 /= x2 =
  genCOp x ++ " = " ++ genCOp x1 ++ ";\n" ++
  "while (mem(" ++ genCOp x ++ ") != 0) {\n" ++
  doGenCCode es ++
  genCOp x ++ " = " ++ genCOp x2 ++ ";\n" ++
  "}\n" ++
  doGenCCode es'
doGenCCode (GetChar x:es) = "mem(" ++ genCOp x ++ ") = getchar();\n" ++ doGenCCode es
doGenCCode (PutChar x:es) = "putchar(mem(" ++ genCOp x ++ "));\n" ++ doGenCCode es
doGenCCode (Kill src Nothing:es) = doGenCCode es
doGenCCode (Kill src (Just dst):es) = genCOp dst ++ " = " ++  genCOp src ++ ";\n" ++ doGenCCode es
doGenCCode (MOV dst src:es) = genCOp dst ++ " = " ++ genCOp src ++ ";\n" ++ doGenCCode es
doGenCCode (LOOPNZ x es:es') = error "doGenCCode: LOOPNZ"

genCOp (Var n) = 'x':show n
genCOp (Imm n) = '(':(show n ++ ")")
genCOp (Reg n) = error "genCOp: Reg"
genCOp (Local n) = "locals[" ++ show n ++ "]"
genCOp (Mem (Var n)) = "mem(x" ++ show n ++ ")"
genCOp (Mem op) = error "genCOp: Mem " ++ show op

data StLife = StLife { nestLevel :: Int
                     , livingLevel :: [(VX86Op, Int)]
                     , toBeExtended :: [(Int, VX86Op)] }
            deriving (Show, Generic)

instance Out StLife

insertKill = (`evalState` (StLife 0 [(Var 0, 0)] [])) . doExtend .
             (`evalState` []) . doInsert

modifyNestLevel f = modify $ \st -> st { nestLevel = f (nestLevel st )}
modifyLivingLevel f = modify $ \st -> st { livingLevel = f (livingLevel st) }
modifyToBeExtended f = modify $ \st -> st { toBeExtended = f (toBeExtended st )}

born op = do
  currLevel <- nestLevel `liftM` get
  modifyLivingLevel ((op, currLevel):)

doExtend [] = return []
doExtend (LetAdd x y z:es) = (LetAdd x y z:) `liftM` (born x >> doExtend es)
doExtend (Let x y:es) = (Let x y:) `liftM` (born x >> doExtend es)
doExtend (While x (x1, x2) es:es') = do
  when (x1 /= x2) (born x)
  currLevel <- nestLevel `liftM` get
  modifyNestLevel (+1)
  es'' <- doExtend es
  modifyNestLevel (subtract 1)
  ops <- (filter ((== currLevel) . fst) . toBeExtended) `liftM` get
  modifyToBeExtended (\\ ops)
  es''' <- doExtend es'
  let kills = map (`Kill` Nothing) $ map snd ops
  return $ (While x (x1, x2) es'':kills) ++ es'''
doExtend (GetChar x:es) = (GetChar x:) `liftM` doExtend es
doExtend (PutChar x:es) = (PutChar x:) `liftM` doExtend es
doExtend (Kill src Nothing:es) = do
  currLevel <- nestLevel `liftM` get
  Just opLevel <- (lookup src . livingLevel) `liftM` get
  if opLevel >= currLevel
    then (Kill src Nothing:) `liftM` doExtend es
    else modifyToBeExtended ((opLevel, src):) >> doExtend es
doExtend (Kill src (Just op):es) = error ("doExtend: Kill " ++ show (src, Just op))
doExtend (MOV dst src:es) = (MOV dst src:) `liftM` doExtend es
doExtend (LOOPNZ x es:es') = error ("doExtend: LOOPNZ " ++ show x)

defined :: (MonadState [VX86Op] m) => VX86Op -> m ()
defined op = do
  rs <- get
  if op `notElem` rs
    then error ("defined: " ++ show op) -- Check for defined but not used vars
    else modify $ filter (/= op)

killVar :: (MonadState [VX86Op] m) => VX86Op -> VX86 -> m VX86
killVar (Mem op) es = killVar op es
killVar op@(Var _) es = do
  rs <- get
  if op `elem` rs
    then return es
    else modify (op:) >> return (Kill op Nothing:es)
killVar _ es = return es

doInsert [] = return []
doInsert (LetAdd x y z:es) = do
  es' <- killVar y =<< killVar z =<< doInsert es
  defined x
  return (LetAdd x y z:es')
doInsert (Let x y:es) = do
  es' <- killVar y =<< doInsert es
  defined x
  return (Let x y:es')
doInsert (While x (x1, x2) es:es') = do
  es''' <- killVar x1 =<< killVar x2 =<< doInsert es'
  es'' <- doInsert es
  when (x1 /= x2) (defined x)
  return (While x (x1, x2) es'':es''')
doInsert (GetChar x:es) =
  return . (GetChar x:) =<< killVar x =<< doInsert es
doInsert (PutChar x:es) =
  return . (PutChar x:) =<< killVar x =<< doInsert es
doInsert (Kill src dst:es) = do
  es' <- doInsert es
  _ <- killVar src es
  return $ Kill src dst:es'
doInsert (MOV dst src:es) =
  return . (MOV dst src:) =<< killVar dst =<< killVar src =<< doInsert es
doInsert (LOOPNZ x es:es') = error ("doInsert: LOOPNZ " ++ show x)

activeVarLimit = 5

data StActive = StActive { localNum :: Int
                         , opNum :: Int
                         , varLocal :: [(VX86Op, VX86Op)]
                         , activeVar :: [(VX86Op, VX86Op)] }
              deriving (Show, Generic)

instance Out StActive

modifyOpNum f = modify $ \st -> st { opNum = f (opNum st) }
modifyLocalNum f = modify $ \st -> st { localNum = f (localNum st) }
modifyVarLocal f = modify $ \st -> st { varLocal = f (varLocal st) }
modifyActiveVar f = modify $ \st -> st { activeVar = f (activeVar st) }

spill es = do
  (rs, vs) <- (activeVar &&& varLocal) `liftM` get
  let (r, r') = findLastUse rs . map stripMem . useSeq $ es
      stripMem (Mem op) = op
      stripMem op = op

      findLastUse (r:_) [] = r
      findLastUse [r] _ = r
      findLastUse rs (u:us) =
        findLastUse (filter ((/= u) . fst) rs) us

      useSeq [] = []
      useSeq (LetAdd x y z:es) = y:z:useSeq es
      useSeq (Let x y:es) = y:useSeq es
      useSeq (While x (x1, x2) es:es')
        | x1 == x2 = (x1:useSeq es) ++ (x2:useSeq es')
        | otherwise = (x:x1:useSeq es) ++ (x2:useSeq es')
      useSeq (GetChar x:es) = x:useSeq es
      useSeq (PutChar x:es) = x:useSeq es
      useSeq (Kill src dst:es) = src:useSeq es
      useSeq (MOV dst src:es) = dst:src:useSeq es
      useSeq (LOOPNZ x es:es') = error "useSeq: LOOPNZ"
  kills [Kill r Nothing]
  case lookup r vs of
    Just _ -> return [] -- not Kill r' Nothing; no need Kill after alloc
    Nothing -> do
      n <- localNum `liftM` get
      modifyLocalNum (+1)
      modifyVarLocal ((r, Local n):)
      return [Kill r' (Just (Local n))]

activate op@(Mem v) es = first Mem `liftM` activate v es
activate op@(Var x) es = do
  rs <- activeVar `liftM` get
  let load = do
        vs <- varLocal `liftM` get
        let v = maybe err id (lookup op vs)
            err = error ("activate: " ++ show op ++ " not found")
        n <- opNum `liftM` get
        modifyOpNum (+1)
        let op' = Var n
        modifyActiveVar ((op, op'):)
        return (op', [Let op' v])
  case lookup op rs of
    Just op' -> return (op', [])
    Nothing
      | length rs < activeVarLimit -> load
      | otherwise -> spill es >>= \p -> second (p ++) `liftM` load
activate op es = return (op, [])

create x es = do
  rs <- activeVar `liftM` get
  p <- if length rs < activeVarLimit then return [] else spill es
  modifyActiveVar ((x,x):)
  return p

kills (Kill x _:es) = do
  modifyActiveVar $ filter ((/= x) . fst)
  kills es
kills _ = return ()

eraseDMailTo x world = do
  world' <- get
  put $ world' { varLocal = varLocal world, activeVar = activeVar world }
  let getSaved op = v where Just v = lookup op (varLocal world')
      reloads = (filter ((/= x) . fst) $ activeVar world) \\ activeVar world'
      reload (op, op') = Let op' (getSaved op)
      shifts = concatMap
                 (\(op, op') -> case lookup op (activeVar world') of
                   Just op'' | op' /= op'' -> [(op', op'')]
                   _ -> [])
                 (activeVar world)
  return $ map (uncurry Let) shifts ++ map reload reloads

limitActiveVars es = evalState (doLimit es) (StActive 0 nextOp [] actives) where
  nextOp = 1 + foldrOp maxVar max 0 es
  maxVar (Var n) m = n `max` m
  maxVar (Mem op) m = maxVar op m
  maxVar _ m = m
  actives = [(Var 0, Var 0)]

doLimit es0@[] = return []
doLimit es0@(LetAdd x y z:es) = do
  (y', p1) <- activate y es0
  (z', p2) <- activate z es0
  kills es
  p3 <- create x es
  es' <- doLimit es
  return $ p1 ++ p2 ++ p3 ++ (LetAdd x y' z':es')
doLimit es0@(Let x y:es) = do
  (y', p1) <- activate y es0
  kills es
  p2 <- create x es
  es' <- doLimit es
  return $ p1 ++ p2 ++ (Let x y':es')
doLimit es0@(While x (x1, x2) es:es') | x1 == x2 = do
  (x1', p1) <- activate x1 es0
  world <- get
  es'' <- doLimit es
  p2 <- eraseDMailTo x world -- assumption: `x` is not used
  kills es'
  es''' <- doLimit es'
  return $ p1 ++ (While x (x1', x1') (es'' ++ p2):es''')
doLimit es0@(While x (x1, x2) es:es') | x1 /= x2 = do
  (x1', p1) <- activate x1 es0
  p2 <- create x es0
  world <- get
  es'' <- doLimit es
  (x2', p3) <- activate x2 es'
  p4 <- eraseDMailTo x world
  kills es'
  es''' <- doLimit es'
  return $ p1 ++ p2 ++ (While x (x1', x2') (es'' ++ p3 ++ p4):es''')
doLimit es0@(GetChar x:es) = do
  (x', p1) <- activate x es0
  kills es
  es' <- doLimit es
  return $ p1 ++ (GetChar x':es')
doLimit es0@(PutChar x:es) = do
  (x', p1) <- activate x es0
  kills es
  es' <- doLimit es
  return $ p1 ++ (PutChar x':es')
doLimit es0@(Kill src (Just op):es) = error ("doLimit: Kill " ++ show (src, Just op))
doLimit es0@(Kill src Nothing:es) = doLimit es
doLimit es0@(MOV dst src:es) = do
  (dst', p1) <- activate dst es0
  (src', p2) <- activate src es0
  kills es
  es' <- doLimit es
  return $ p1 ++ p2 ++ (MOV dst' src':es')
doLimit es0@(LOOPNZ x es:es') = error "doLimit: LOOPNZ"

fn [] = undefined
fn (LetAdd x y z:es) = undefined
fn (Let x y:es) = undefined
fn (While x (x1, x2) es:es') = undefined
fn (GetChar x:es) = undefined
fn (PutChar x:es) = undefined
fn (Kill src dst:es) = undefined
fn (MOV dst src:es) = undefined
fn (LOOPNZ x es:es') = undefined

remWhile :: VX86 -> VX86
remWhile [] = []
remWhile (While x (x1, x2) es:es')
  | x1 == x2 =
      LOOPNZ (Mem x1) (remWhile es):
      remWhile es'
  | otherwise =
      MOV x x1:
      LOOPNZ (Mem x)
        (remWhile es ++
        [MOV x x2]):
      remWhile es'
remWhile (e:es) = e:remWhile es
