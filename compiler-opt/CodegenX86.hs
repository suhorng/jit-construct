{-# LANGUAGE FlexibleContexts, DeriveGeneric #-}

module CodegenX86 where

import qualified CoreExpr as E

import Control.Arrow (first, second, (&&&), (***))
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Except
import Data.List ((\\), partition)
import Text.PrettyPrint.GenericPretty

{-
fn [] = undefined
fn (LetAdd x y z:es) = undefined
fn (Let x y:es) = undefined
fn (While x (x1, x2) es []:es') = undefined
fn (GetChar x:es) = undefined
fn (PutChar x:es) = undefined
fn (Kill src dst:es) = undefined
fn (MOV dst src:es) = undefined
fn (LOOPNZ lbl x es:es') = undefined
-}
type VX86 = [VX86Inst]

foldrOp f g e [] = e
foldrOp f g e (LetAdd x y z:es) = f x (f y (f z (foldrOp f g e es)))
foldrOp f g e (LetMul x y z:es) = f x (f y (f z (foldrOp f g e es)))
foldrOp f g e (Let x y:es) = f x (f y (foldrOp f g e es))
foldrOp f g e (While x (x1, x2) es xs:es') = f x (f x1 (f x2 (g (foldrOp f g e es) (foldr (\(a1, a2) b -> f a1 (f a2 b)) (foldrOp f g e es') xs))))
foldrOp f g e (GetChar x:es) = f x (foldrOp f g e es)
foldrOp f g e (PutChar x:es) = f x (foldrOp f g e es)
foldrOp f g e (Kill src Nothing:es) = f src (foldrOp f g e es)
foldrOp f g e (Kill src (Just dst):es) = f src (f dst (foldrOp f g e es))
foldrOp f g e (MOV dst src:es) = f dst (f src (foldrOp f g e es))
foldrOp f g e (LOOPNZ lbl x es:es') = f x (g (foldrOp f g e es) (foldrOp f g e es'))

data VX86Inst =
    LetAdd VX86Op VX86Op VX86Op
  | LetMul VX86Op VX86Op VX86Op
  | Let VX86Op VX86Op
  | While VX86Op (VX86Op, VX86Op) VX86 [(VX86Op, VX86Op)]
  | GetChar VX86Op
  | PutChar VX86Op
  | Kill VX86Op (Maybe VX86Op)
  | Call String VX86Op
  | LEA VX86Op VX86Op
  | ADD VX86Op VX86Op
  | MUL VX86Op VX86Op VX86Op
  | MOV VX86Op VX86Op
  | LOOPNZ Int VX86Op VX86
  deriving (Eq, Show, Generic)

data VX86Op =
    Var Int
  | Imm Int
  | Reg Int
  | Local Int
  | Mem VX86Op
  | Indir String VX86Op VX86Op
  deriving (Eq, Show, Generic)

instance Out VX86Inst
instance Out VX86Op

isReg (Reg _) = True
isReg _ = False

injVX86 :: E.Prog -> VX86
injVX86 (E.Let x (E.Add (E.Opr y) (E.Opr z)) e) = LetAdd (Var x) (injOp y) (injOp z):injVX86 e
injVX86 (E.Let x (E.Mul (E.Opr y) (E.Opr z)) e) = LetMul (Var x) (injOp y) (injOp z):injVX86 e
injVX86 (E.Let x c e) = error ("injVX86: Non-flatten: " ++ show c)
injVX86 (E.Load x op e) = Let (Var x) (Mem (injOp op)):injVX86 e
injVX86 (E.Store x op e) = MOV (Mem (injOp x)) (injOp op):injVX86 e
injVX86 (E.While x (x1, x2) e e') =
  if x1 == x2 && (use x es || use x es') then error ("injVX86: While: use of " ++ show x) else
  While (Var x) (Var x1, Var x2) es []:
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

data StLife = StLife { nestLevel :: Int
                     , livingLevel :: [(VX86Op, Int)]
                     , toBeExtended :: [(Int, VX86Op)] }
            deriving (Show, Generic)

instance Out StLife

modifyNestLevel f = modify $ \st -> st { nestLevel = f (nestLevel st )}
modifyLivingLevel f = modify $ \st -> st { livingLevel = f (livingLevel st) }
modifyToBeExtended f = modify $ \st -> st { toBeExtended = f (toBeExtended st )}

insertKill = (`evalState` (StLife 0 [(Var 0, 0)] [])) . doExtend .
             (`evalState` []) . doInsert

born op = do
  currLevel <- nestLevel `liftM` get
  modifyLivingLevel ((op, currLevel):)

doExtend [] = return []
doExtend (LetAdd x y z:es) = (LetAdd x y z:) `liftM` (born x >> doExtend es)
doExtend (LetMul x y z:es) = (LetMul x y z:) `liftM` (born x >> doExtend es)
doExtend (Let x y:es) = (Let x y:) `liftM` (born x >> doExtend es)
doExtend (While x (x1, x2) es xs:es') = do
  when (x1 /= x2) (born x)
  currLevel <- nestLevel `liftM` get
  modifyNestLevel (+1)
  es'' <- doExtend es
  modifyNestLevel (subtract 1)
  ops <- (filter ((== currLevel) . fst) . toBeExtended) `liftM` get
  modifyToBeExtended (\\ ops)
  es''' <- doExtend es'
  let kills = map (`Kill` Nothing) $ map snd ops
  return $ (While x (x1, x2) es'' xs:kills) ++ es'''
doExtend (GetChar x:es) = (GetChar x:) `liftM` doExtend es
doExtend (PutChar x:es) = (PutChar x:) `liftM` doExtend es
doExtend (Kill src Nothing:es) = do
  currLevel <- nestLevel `liftM` get
  Just opLevel <- (lookup src . livingLevel) `liftM` get
  if opLevel >= currLevel
    then (Kill src Nothing:) `liftM` doExtend es
    else modifyToBeExtended ((opLevel, src):) >> doExtend es
doExtend (Kill src dst:es) = (Kill src dst:) `liftM` doExtend es
doExtend (MOV dst src:es) = (MOV dst src:) `liftM` doExtend es
doExtend (LOOPNZ lbl x es:es') = error ("doExtend: LOOPNZ " ++ show x)

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
doInsert (LetMul x y z:es) = do
  es' <- killVar y =<< killVar z =<< doInsert es
  defined x
  return (LetMul x y z:es')
doInsert (Let x y:es) = do
  es' <- killVar y =<< doInsert es
  defined x
  return (Let x y:es')
doInsert (While x (x1, x2) es xs:es') = do
  es''' <- killVar x1 =<< killVar x2 =<< doInsert es'
  modify (\\ map fst xs)
  es'' <- doInsert es
  when (x1 /= x2) (defined x)
  return (While x (x1, x2) es'' xs:es''')
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
doInsert (LOOPNZ lbl x es:es') = error ("doInsert: LOOPNZ " ++ show x)

activeVarLimit = 4

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

useSeq [] = []
useSeq (LetAdd x y z:es) = y:z:useSeq es
useSeq (LetMul x y z:es) = y:z:useSeq es
useSeq (Let x y:es) = y:useSeq es
useSeq (While x (x1, x2) es []:es')
  | x1 == x2 = (x1:useSeq es) ++ (x2:useSeq es')
  | otherwise = (x:x1:useSeq es) ++ (x2:useSeq es')
useSeq (GetChar x:es) = x:useSeq es
useSeq (PutChar x:es) = x:useSeq es
useSeq (Kill src dst:es) = src:useSeq es
useSeq (MOV dst src:es) = dst:src:useSeq es
useSeq (LOOPNZ lbl x es:es') = error "useSeq: LOOPNZ"

stripMem (Mem op) = op
stripMem op = op

spillAny es = do
  rs <- activeVar `liftM` get
  nextUses <- ask
  let (r, _) = findLastUse rs . (++ nextUses) . map stripMem . useSeq $ es
      findLastUse (r:_) [] = r
      findLastUse [r] _ = r
      findLastUse rs (u:us) = findLastUse (filter ((/= u) . fst) rs) us
  vs <- varLocal `liftM` get
  case lookup r vs of
    Just _ -> kills [Kill r Nothing]
    Nothing -> throwError r --spillOne r

spills xs m = m `catchError` \x -> do
  when (x `notElem` map stripMem xs) $ throwError x
  p <- spillOne x
  es' <- spills xs m
  return $ p ++ es'

spillOne r = do
  vs <- varLocal `liftM` get
  killed <- kills [Kill r Nothing]
  case killed of
    [Kill _ Nothing] -> return ()
    _ -> get >>= \st -> error $ pretty ("spillOne", r, killed, st)
  let [Kill r' Nothing] = killed
  case lookup r vs of
    Just _ -> error $ pretty ("spillOne lookup Just", r, vs, killed)
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
      | otherwise -> spillAny es >>= \p -> second (p ++) `liftM` load
activate op es = return (op, [])

create x es = do
  rs <- activeVar `liftM` get
  p <- if length rs < activeVarLimit then return [] else spillAny es
  modifyActiveVar ((x,x):)
  return p

kills (Kill src dst:es) = do
  rs <- activeVar `liftM` get
  case lookup src rs of
    Just src' -> do
      modifyActiveVar $ filter ((/= src) . fst)
      (Kill src' dst:) `liftM` kills es
    Nothing -> kills es
kills _ = return []

eraseDMailTo x' world = do
  world' <- get
  put $ world { opNum = opNum world' }
  let getSaved op = v where Just v = lookup op (varLocal world')
      avoid
        | Just x <- x' = filter ((/= x) . fst)
        | Nothing <- x' = id
      reloads = avoid (activeVar world) \\ activeVar world'
      reload (op, op') = (op', getSaved op)
      shifts = concatMap
                 (\(op, op') -> case lookup op (activeVar world') of
                   Just op'' | op' /= op'' -> [(op', op'')]
                   _ -> [])
                 (avoid (activeVar world))
  return $ shifts ++ map reload reloads

limitActiveVars es = getRight . runExcept . (`evalStateT` st0) . (`runReaderT` []) $ spills [Var 0] (doLimit es) where
  getRight (Right a) = a
  getRight (Left e) = error $ "getRight: " ++ show e
  st0 = StActive 0 nextOp [] actives
  nextOp = 1 + foldrOp maxVar max 0 es
  maxVar (Var n) m = n `max` m
  maxVar (Mem op) m = maxVar op m
  maxVar _ m = m
  actives = [(Var 0, Var 0)]

doLimit es0@[] = return []
doLimit es0@(LetAdd x y z:es) = do
  (y', p1) <- activate y es0
  (z', p2) <- activate z es0
  p4 <- kills es
  p3 <- create x es0
  es' <- spills [x,y,z] (doLimit es)
  return $ p1 ++ p2 ++ p3 ++ (LetAdd x y' z':p4) ++ es'
doLimit es0@(LetMul x y z:es) = do
  (y', p1) <- activate y es0
  (z', p2) <- activate z es0
  p4 <- kills es
  p3 <- create x es0
  es' <- spills [x,y,z] (doLimit es)
  return $ p1 ++ p2 ++ p3 ++ (LetMul x y' z':p4) ++ es'
doLimit es0@(Let x y:es) = do
  st <- get
  (y', p1) <- activate y es0
  p3 <- kills es
  p2 <- create x es0
  es' <- spills [x,y] (doLimit es)
  return $ p1 ++ p2 ++ (Let x y':p3) ++ es'
doLimit es0@(While x (x1, x2) es []:es') | x1 == x2 = do
  (x1', p1) <- activate x1 es0
  world <- get
  es'' <- local (++ (map stripMem $ x2:useSeq es')) $ spills [x1] (doLimit es)
  xs <- eraseDMailTo Nothing world -- assumption: `x` is not used
  p2 <- kills es'
  es''' <- doLimit es'
  return $ p1 ++ (While x (x1', x1') es'' xs:p2) ++ es'''
doLimit es0@(While x (x1, x2) es []:es') | x1 /= x2 = do
  (x1', p1) <- activate x1 es0
  p2 <- create x es0
  world <- get
  es'' <- local (++ (map stripMem $ x2:useSeq es')) $ spills [x] (doLimit es)
  (x2', p3) <- activate x2 es'
  xs <- eraseDMailTo (Just x) world
  p4 <- kills es'
  es''' <- spills [x] (doLimit es')
  return $ p1 ++ p2 ++ (While x (x1', x2') (es'' ++ p3) xs:p4) ++ es'''
doLimit es0@(GetChar x:es) = do
  (x', p1) <- activate x es0
  p2 <- kills es
  es' <- spills [x] (doLimit es)
  return $ p1 ++ (GetChar x':p2) ++ es'
doLimit es0@(PutChar x:es) = do
  (x', p1) <- activate x es0
  p2 <- kills es
  es' <- spills [x] (doLimit es)
  return $ p1 ++ (PutChar x':p2) ++ es'
doLimit es0@(Kill src (Just op):es) = error ("doLimit: Kill " ++ show (src, Just op))
doLimit es0@(Kill src Nothing:es) = doLimit es
doLimit es0@(MOV dst src:es) = do
  (dst', p1) <- activate dst es0
  (src', p2) <- activate src es0
  p3 <- kills es
  es' <- spills [dst,src] (doLimit es)
  return $ p1 ++ p2 ++ (MOV dst' src':p3) ++ es'
doLimit es0@(LOOPNZ lbl x es:es') = error "doLimit: LOOPNZ"

data StReg = StReg { freeRegs :: [VX86Op]
                   , varAlloc :: [(VX86Op, VX86Op)] }
            deriving (Show, Generic)

instance Out StReg

modifyFreeRegs f = modify $ \st -> st { freeRegs = f (freeRegs st) }
modifyVarAlloc f = modify $ \st -> st { varAlloc = f (varAlloc st) }

collapse es = doRename es where
  StReg rs als = execState (doCollapse [] es) (StReg rs0 [(Var 0, rx0)])
  rs0 = map Reg [0..3] \\ [rx0]
  rx0 = Reg 1

  renamed (Mem op) = Mem (renamed op)
  renamed op@(Var _)
    | Just r <- lookup op als = r
    | otherwise = error $ "renamed: " ++ show op ++ "\n\n" ++ show als
  renamed op = op

  doRename [] = []
  doRename (LetAdd x y z:es) = LetAdd (renamed x) (renamed y) (renamed z):doRename es
  doRename (LetMul x y z:es) = LetMul (renamed x) (renamed y) (renamed z):doRename es
  doRename (Let x y:es) = Let (renamed x) (renamed y):doRename es
  doRename (While x (x1, x2) es xs:es') =
    While (if x1 == x2 then x else renamed x) (renamed x1, renamed x2)
      (doRename es)
      (map (renamed *** renamed) xs):
    doRename es'
  doRename (GetChar x:es) = GetChar (renamed x):doRename es
  doRename (PutChar x:es) = PutChar (renamed x):doRename es
  doRename (Kill src Nothing:es) = doRename es
  doRename (Kill src dst@(Just (Local _)):es) = Kill (renamed src) dst:doRename es
  doRename (Kill src dst:es) = error ("doRename: Kill " ++ show (src, dst))
  doRename (MOV dst src:es) = MOV (renamed dst) (renamed src):doRename es
  doRename (LOOPNZ lbl x es:es') = error ("doRename: LOOPNZ " ++ show x)

allocate hints (Mem op) = allocate hints op
allocate hints op@(Var _) = do
  (als, rs) <- (varAlloc &&& freeRegs) `liftM` get
  case lookup op als of
    Just r -> modifyFreeRegs (filter (/= r)) >> when (r `notElem` rs) (error ("allocate: repeated: " ++ show op ++ " " ++ show rs ++ "\n" ++ show als))
    Nothing -> do
      when (null rs) $ error ("allocate: " ++ show op ++ "\n" ++ show als)
      let getAlloc op
            | Just r' <- lookup op als = [r']
            | otherwise = []
          ravail = filter (`elem` rs) . concatMap getAlloc . map stripMem $ hints
          (r':_)
            | [] <- ravail = rs
            | otherwise = ravail
      modifyFreeRegs $ filter (/= r')
      modifyVarAlloc ((op, r'):)
allocate hints op = return ()

release op@(Var _) = do
  (als, rs) <- (varAlloc &&& freeRegs) `liftM` get
  case lookup op als of
    Just r -> modifyFreeRegs (r:) >> when (r `elem` rs) (error ("release: repeated: " ++ show op ++ " " ++ show rs ++ "\n" ++ show als))
    Nothing -> error $ "release Nothing: " ++ show op
release (Local _) = return ()

releases (Kill src Nothing:es) = release src >> releases es
releases (Kill src dst@(Just _):es) = (Kill src dst:) `liftM` releases es
releases es = return es

doCollapse hints [] = return ()
doCollapse hints (LetAdd x y z:es) = do
  es' <- releases es
  allocate (y:z:hints) x
  doCollapse [] es'
doCollapse hints (LetMul x y z:es) = do
  es' <- releases es
  allocate (y:z:hints) x
  doCollapse [] es'
doCollapse hints (Let x y:es) = do
  es' <- releases es
  allocate (y:hints) x
  doCollapse [] es'
doCollapse hints (While x (x1, x2) es xs:es') = do
  when (x1 /= x2) (allocate [x1] x)
  world <- get
  releases es >>= doCollapse []
  modify $ \world' -> world' { freeRegs = freeRegs world }
  let x2Defined [] = False
      x2Defined (LetAdd op _ _:es) = op == x2 || x2Defined es
      x2Defined (LetMul op _ _:es) = op == x2 || x2Defined es
      x2Defined (Let op _:es) = op == x2 || x2Defined es
      x2Defined (While op _ _ _:es) = op == x2 || x2Defined es
      x2Defined (_:es) = x2Defined es
      removeKillX2 (e@(Kill src dst):es)
        | src == x2, Nothing <- dst = removeKillX2 es
        | otherwise = e:removeKillX2 es
      removeKillX2 es = es
  releases (if x2Defined es then removeKillX2 es' else es') >>= doCollapse []
doCollapse hints (GetChar x:es) = releases es >>= doCollapse []
doCollapse hints (PutChar x:es) = releases es >>= doCollapse []
doCollapse hints (Kill src (Just _):es) = release src >> doCollapse (src:hints) es
doCollapse hints (Kill src dst:es) = error ("doCollapse: Kill " ++ show (src, dst))
doCollapse hints (MOV dst src:es) = releases es >>= doCollapse []
doCollapse hints (LOOPNZ lbl x es:es') = error ("doCollapse: LOOPNZ " ++ show x)

genFixWorld = doGenFixWorld . filter (not . uncurry (==))

breakLoopTmp = Reg 5

doGenFixWorld [] = []
doGenFixWorld ops0 =
  case findOut0 [] ops0 of
    (Nothing, (op, op'):ops) -> (breakLoopTmp, op):(op, op'):insertBreakLoop op (doGenFixWorld ops)
    (Just (op, op'), ops) -> (op, op'):doGenFixWorld ops

findOut0 ops' [] = (Nothing, ops')
findOut0 ops' ((op, op'):ops) =
  if op `elem` map snd ops || op `elem` map snd ops'
  then findOut0 (ops' ++ [(op, op')]) ops
  else (Just (op, op'), ops' ++ ops)

insertBreakLoop op0 [] = error $ "insertBreakLoop: " ++ show op0
insertBreakLoop op0 ((op, op'):ops)
  | op0 == op' = (op, breakLoopTmp):ops
  | otherwise = (op, op'):insertBreakLoop op0 ops

freshLabel :: (MonadState Int m) => m Int
freshLabel = do
  n <- get
  modify (+1)
  return n

genCode = (`evalState` 0) . doGenCode

doGenCode (Kill src (Just dst):Let src' dst':es)
  | src == src' && dst == dst' = (MOV dst src:) `liftM` doGenCode es
doGenCode [] = return []
doGenCode (LetAdd dst src1 src2:es)
  | dst == src1 = (ADD dst src2:) `liftM` doGenCode es
  | dst == src2 = (ADD dst src1:) `liftM` doGenCode es
  | otherwise = (LEA dst (Indir "" src1 src2):) `liftM` doGenCode es
doGenCode (LetMul dst src1 src2:es) = (MUL dst src2 src1:) `liftM` doGenCode es
doGenCode (Let dst src:es) = (MOV dst src:) `liftM` doGenCode es
doGenCode (While x (x1, x2) es xs:es') | x1 /= x2 || isReg x = do
  lbl <- freshLabel
  es'' <- doGenCode es
  let xs' = map (uncurry MOV) $ genFixWorld ((x,x2):xs)
  es''' <- doGenCode es'
  return $ MOV x x1:LOOPNZ lbl (Mem x) (es'' ++ xs'):es'''
doGenCode (While x (x1, x2) es xs:es') | x1 == x2 = do
  lbl <- freshLabel
  es'' <- doGenCode es
  let xs' = map (uncurry MOV) $ genFixWorld xs
  es''' <- doGenCode es'
  return $ LOOPNZ lbl (Mem x1) (es'' ++ xs'):es'''
doGenCode (GetChar x:es) = (Call "_rt_getchar" x:) `liftM` doGenCode es
doGenCode (PutChar x:es) = (Call "_rt_putchar" x:) `liftM` doGenCode es
doGenCode (Kill src Nothing:es) = doGenCode es
doGenCode (Kill src (Just dst):es) = (MOV dst src:) `liftM` doGenCode es
doGenCode (MOV dst src:es) = (MOV dst src:) `liftM` doGenCode es
doGenCode (LOOPNZ lbl x es:es') = error $ "LOOPNZ: " ++ show x

regs = ["eax", "ebx", "ecx", "edx", "esi", "[_tmp]", "edi"]
regs' = ["al", "bl", "cl", "dl", error "regs': esi", error "regs': [_tmp]", error "regs': edi"]

printOp0 regs (Imm n) = "(" ++ show n ++ ")"
printOp0 regs (Reg m) = regs!!m
printOp0 regs (Indir s op1 op2) =
  s ++ " [" ++ printOp0 regs op1 ++
            (if op2 /= Imm 0 then " + " ++ printOp0 regs op2 else "") ++
        "]"
printOp0 regs (Local n) = printOp0 regs (Indir "dword" (Reg 6) (Imm (n*4)))
printOp0 regs (Mem op@(Reg m)) | m < activeVarLimit = printOp0 regs (Indir "byte" op (Imm 0))
printOp0 regs op = error "genOp: " ++ show op

printOp = printOp0 regs

printCode es = pre ++ doPrint es ++ post where
  pre  = concat [ "[bits 32]\n"
                , "[section .text]\n"
                , "global _bf_main\n"
                , "extern _putchar\n"
                , "extern _getchar\n"
                , "extern _tmp\n\n"
                , "_rt_putchar:\n"
                , "\tpush  ebp\n"
                , "\tmov   ebp, esp\n"
                , "\tpush  eax\n"
                , "\tpush  ecx\n"
                , "\tpush  edx\n"
                , "\tmov   eax, [ebp + 8]\n"
                , "\tmovzx edx, byte [eax]\n"
                , "\tpush  edx\n"
                , "\tcall  _putchar\n"
                , "\tadd   esp, 4\n"
                , "\tpop   edx\n"
                , "\tpop   ecx\n"
                , "\tpop   eax\n"
                , "\tleave\n"
                , "\tret   4\n\n"
                , "_rt_getchar:\n"
                , "\tpush  ebp\n"
                , "\tmov   ebp, esp\n"
                , "\tpush  eax\n"
                , "\tpush  ecx\n"
                , "\tpush  edx\n"
                , "\tcall  _getchar\n"
                , "\tmov   edx, [ebp + 8]\n"
                , "\tmov   [edx], al\n"
                , "\tpop   edx\n"
                , "\tpop   ecx\n"
                , "\tpop   eax\n"
                , "\tleave\n"
                , "\tret   4\n\n"
                , "_bf_main:\n"
                , "\tpush  ebp\n"
                , "\tmov   ebp, esp\n"
                , "\tpush  ebx\n"
                , "\tpush  edi\n"
                , "\tmov   ebx, [ebp + 8]\n"
                , "\tmov   edi, [ebp + 12]\n" ]
  post = concat [ "\tpop   edi\n"
                , "\tpop   ebx\n"
                , "\tleave\n"
                , "\tret\n" ]

doPrint [] = ""
doPrint (Call flbl op:es) =
  "\tpush  " ++ printOp op ++ "\n" ++
  "\tcall  " ++ flbl ++ "\n" ++
  doPrint es
doPrint (LEA dst src:es) =
  "\tlea   " ++ printOp dst ++ ", " ++ printOp src ++ "\n" ++ doPrint es
doPrint (ADD dst src:es) =
  "\tadd   " ++ printOp dst ++ ", " ++ printOp src ++ "\n" ++ doPrint es
doPrint (MUL dst src1 src2:es) =
  "\timul  " ++ printOp dst ++ ", " ++ printOp src1 ++ ", " ++ printOp src2 ++ "\n" ++ doPrint es
doPrint (MOV dst src@(Mem _):es) =
  "\tmovsx " ++ printOp dst ++ ", " ++ printOp src ++ "\n" ++ doPrint es
doPrint (MOV dst@(Mem _) src:es) =
  "\tmov   " ++ printOp dst ++ ", " ++ printOp0 regs' src ++ "\n" ++ doPrint es
doPrint (MOV dst src:es) =
  "\tmov   " ++ printOp dst ++ ", " ++ printOp src ++ "\n" ++ doPrint es
doPrint (LOOPNZ lbl x es:es') =
  "L" ++ show (lbl*2) ++ ":\n" ++
  "\tcmp   " ++ printOp x ++ ", 0\n" ++
  "\tjz    L" ++ show (lbl*2+1) ++ "\n" ++
  doPrint es ++
  "\tjmp   L" ++ show (lbl*2) ++ "\n" ++
  "L" ++ show (lbl*2+1) ++ ":\n" ++
  doPrint es'
