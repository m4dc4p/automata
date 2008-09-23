{-# OPTIONS_GHC -fglasgow-exts -fbang-patterns #-}
module CoreTest (f)

where

import Data.Bits ((.&.), shiftL, (.|.), bitSize, testBit, clearBit, setBit, Bits(), shiftR, rotateL, shiftL, complement)
import GHC.Base (int2Word#, word2Int#, Int(..), uncheckedShiftRL#, uncheckedShiftL#)


f :: Int -> Int -> Int -> Int -> (Int, Int)
f r1 !width !r2 !leftOver =
  let (# a#, b# #) = fillS r2 0 r1 r1 r2 r2
  in (I# a#, I# b#)
  where
      I# a `unsafeShiftR` I# b = I# (word2Int# (int2Word# a `uncheckedShiftRL#` b))
      I# a `unsafeShiftL` I# b = I# (word2Int# (int2Word# a `uncheckedShiftL#` b))
      w1 = 2 ^ (width * 2 + 1)
      ruleBit :: Int -> Int
      ruleBit 0 = 0 
      ruleBit _ = w1
      fillS !cnt !rule !cellMask !val !currVal !nextVal
          | cnt == 0 = fillE (width - 1) (rule + 1) 2 val nextVal
          | otherwise = 
              let newRuleIdx = ((rule .|. (I# bit#)) `unsafeShiftR` 1) .&. r2
                  bit = ruleBit (currVal .&. cellMask)
                  (I# bit#) = ruleBit (currVal .&. cellMask)
              in {-# CORE "LOOK HERE" #-} fillS (cnt - 1) newRuleIdx (cellMask + 1) val currVal nextVal
      fillE !cnt !rule !cellMask !val !currVal =
                  let (I# val#) = val
                      (I# rule#) = rule
                  in (# val#, rule# #)
