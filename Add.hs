{-# OPTIONS_GHC -fglasgow-exts -fbang-patterns  #-}
module Add (shiftA)

where

import Data.Bits
import GHC.Base (uncheckedShiftRL#, Int(..), word2Int#, int2Word#)

I# a `unsafeShiftR` I# b = I# (word2Int# (int2Word# a `uncheckedShiftRL#` b))

shiftA !a !b !c = a `unsafeShiftR` (b + c)