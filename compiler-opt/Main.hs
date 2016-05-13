{-# LANGUAGE BangPatterns, GADTs, TypeOperators #-}

module Main where

import Brainfsck
import CoreExpr
import Simplifier
import CodegenX86
import CodegenCFromX86

import System.Environment (getArgs)
import System.CPUTime
import System.IO

import Text.Printf
import Text.PrettyPrint.GenericPretty

infixr 2 :::
infixr 2 ::-
infixr 1 +++

data Phases a b where
  Void :: Phases a a
  (:::) :: (String, a -> c) -> Phases c b -> Phases a b
  (::-) :: (String, a -> c, c -> IO ()) -> Phases c b -> Phases a b

(+++) :: Phases a b -> Phases b c -> Phases a c
(p ::: ps) +++ qs = p ::: (ps +++ qs)
(p ::- ps) +++ qs = p ::- (ps +++ qs)
Void +++ qs = qs

runPhases :: Phases a b -> a -> IO b
runPhases Void !a = return a
runPhases ((name, f) ::: xs) !a = do
  hPrintf stderr "%12.3f " . (/ 10^12) . (fromIntegral :: Integer -> Double) =<< getCPUTime
  hPutStrLn stderr name
  runPhases xs (f a)
runPhases ((name, f, act) ::- xs) !a = do
  hPrintf stderr "%12.3f " . (/ 10^12) . (fromIntegral :: Integer -> Double) =<< getCPUTime
  hPutStrLn stderr name
  let !c = f a
  act c
  runPhases xs c

build =
  ("parse", parse, \bfp -> hPutStrLn stderr $ replicate 13 ' ' ++ "length=" ++ show (length bfp)) ::-
  ("construct", construct 0) :::
  Void

basicOpts =
  ("peval", peval) :::
  ("memeval", memeval False) :::
  ("peval", peval) :::
  ("bindeval", bindeval) :::
  Void

codeGen =
  ("injVX86", injVX86) :::
  ("liveness", insertKill) :::
  ("spill", limitActiveVars) :::
  ("assignment", collapse) :::
  ("genCode", genCode) :::
  ("print", CodegenX86.printCode, putStr) ::-
  Void

phases =
  build +++
  basicOpts +++
  ("trivloop", trivloop) ::: Void +++
  basicOpts +++
  ("flatten", flatten) ::: Void +++
  ("commons", commons) ::: Void +++
  basicOpts +++
  ("memeval-diff", memeval True) ::: Void +++
  basicOpts +++
  ("flatten", flatten) ::: Void +++
--  ("print", CoreExpr.printCode, putStr) ::-
  codeGen +++
  ("done", id) :::
  Void

test :: String -> IO ()
test fn = do
  s <- readFile fn
  _ <- runPhases phases s
  return ()

main = getArgs >>= test . head

