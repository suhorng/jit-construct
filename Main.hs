module Main where

import Simplifier (test)
import System.Environment (getArgs)

main = getArgs >>= test . head
