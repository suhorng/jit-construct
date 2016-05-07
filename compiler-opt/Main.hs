{-# LANGUAGE BangPatterns #-}

module Main where

import Brainfsck
import CoreExpr
import Simplifier
import CodegenX86
import CodegenCFromX86

import System.Environment (getArgs)
import System.CPUTime
import System.IO

import Text.PrettyPrint.GenericPretty

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
  hPutStr stderr . show . (/ 10^12) . fromIntegral =<< getCPUTime; hPutStrLn stderr " injx86"
  let !inj = injVX86 ir''''
  hPutStr stderr . show . (/ 10^12) . fromIntegral =<< getCPUTime; hPutStrLn stderr " liveness"
  let !kld = insertKill inj
  --mapM_ pp kld >> putStrLn "======== ^ kld ========="
  hPutStr stderr . show . (/ 10^12) . fromIntegral =<< getCPUTime; hPutStrLn stderr " spill"
  let !lmd = limitActiveVars kld
  --mapM_ pp lmd >> putStrLn "======== ^ lmd ========="
  hPutStr stderr . show . (/ 10^12) . fromIntegral =<< getCPUTime; hPutStrLn stderr " assignment"
  let !col = collapse lmd
  hPutStr stderr . show . (/ 10^12) . fromIntegral =<< getCPUTime; hPutStrLn stderr " gencode"
  --mapM_ pp col >> putStrLn "================="
--  putStr $ genCCode lmd
--{-
  let !asm = genCode col
  hPutStr stderr . show . (/ 10^12) . fromIntegral =<< getCPUTime; hPutStrLn stderr " print"
  putStr $ CodegenX86.printCode asm
---}

main = getArgs >>= testTime . head
