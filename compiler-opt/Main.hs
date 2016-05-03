{-# LANGUAGE BangPatterns #-}

module Main where

import Brainfsck
import CoreExpr
import Simplifier
import CodegenX86

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
  hPutStr stderr . show . (/ 10^12) . fromIntegral =<< getCPUTime; hPutStrLn stderr " done"
  --print ir''''
  --putStr $ printCode ir''''
  let inj = injVX86 ir''''
      kld = insertKill inj
      lmd = limitActiveVars kld
      kld2 = insertKill lmd
      col = collapse kld2
  putStrLn (genCCode col)

main = getArgs >>= testTime . head
