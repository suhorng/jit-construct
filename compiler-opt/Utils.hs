module Utils where

import Data.Word

type Mem = [Word8]

new    n          = replicate n 0
deref  mem addr   = mem!!addr
update mem addr x = prefix ++ (x:suffix) where
  (prefix, _:suffix) = splitAt addr mem
mmodify mem addr f = update mem addr (f (deref mem addr))
