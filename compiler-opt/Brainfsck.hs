module Brainfsck where

import Utils
import Data.Char (chr, ord)

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

interp :: Int -> Brainfsck -> String -> String
interp n = interp' (new n) 0 where
  ord' = fromIntegral . ord
  chr' = chr . fromIntegral

  interp' :: Mem -> Int -> Brainfsck -> String -> String
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
