module Main where

import Simplifier (test_, testTime)
import System.Environment (getArgs)

main = getArgs >>= testTime . head
