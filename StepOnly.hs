{-# OPTIONS_GHC -fglasgow-exts -fbang-patterns  #-}
module StepOnly (stepWithUArray)

where

import Data.Array.Base (unsafeAt, unsafeWrite, UArray(..))
import Data.Array.IArray (bounds)
import GHC.ST (ST)
import qualified Data.Array.ST as ST (runSTUArray, newArray_, STUArray)
import Data.Bits ((.&.), shiftL, (.|.), bitSize, testBit, clearBit, setBit, Bits(), shiftR, rotateL, shiftL, complement)
import GHC.Base (int2Word#, word2Int#, Int(..), indexWordArray#, or#, and#, uncheckedShiftRL#, uncheckedShiftL#,
  (-#), (==#), (+#), ByteArray#, Word#, Int#, eqWord#, minusWord#)

data Rule = Rule { ruleWidth :: !Int, rules :: !(UArray Int Int) }

h1 :: Int
h1 = {-# CORE "h1" #-} clearBit (complement 0) ((bitSize (undefined :: Int)) - 1) -- 2147483647 

intSize :: Int
intSize = bitSize (undefined :: Int) -- 32 

stepWithUArray :: Rule -> Int -> UArray Int Int -> UArray Int Int
stepWithUArray rule@(Rule !width@(I# width#) !rules) !leftOver@(I# leftOver#) !row =
  ST.runSTUArray fillRow
  -- Apply rule to each cell in CA. 
  where
      (lower, upper@(I# upper#)) = bounds row
      w2 :: Int
      w2 = 2 ^ (width + 1)
      -- Get the value of the rule for the leftmost cell. This only
      -- works if leftOver > width
      firstRule
          | leftOver > width =
              -- Get initial value by shifting upper array (leftover - width) amount. Need
              -- to mask off extra bits once shifted too.
              let leftVal = ((unsafeAt row upper) `shiftR` (leftOver - width)) .&. (2 ^ width - 1)
                  -- Right side of rule is current cell plus neighbors to right,
                  -- thus mask all but (width + 1) bits.
                  rightVal = (unsafeAt row lower) .&. (w2 - 1)
              in leftVal .|. (rightVal `shiftL` width)
          | otherwise = error "leftover less than width!" -- leftover less than width bad.
      fillRow :: forall s. ST s (ST.STUArray s Int Int)
      fillRow = {-# SCC "step_fillRow" #-}
          do
            arr <- ST.newArray_ (lower,upper)
            let
              {-# INLINE unsafeShiftR #-}
              I# a `unsafeShiftR` I# b = I# (word2Int# (int2Word# a `uncheckedShiftRL#` b))
              {-# INLINE unsafeShiftL #-}
              I# a `unsafeShiftL` I# b = I# (word2Int# (int2Word# a `uncheckedShiftL#` b))
              w1 :: Int
              w1 = 2 ^ (width * 2 + 1)
              (I# intSize#) = intSize
              ruleStartMask = w2
              ruleShiftMask = w1 - 1
              -- Return value which, when masked to ruleIdx, will allow
              -- ruleIdx to be shifted right one place and then have the correct value.
              ruleBit :: Int -> Int
              ruleBit 0 = 0 
              ruleBit _ = w1
              ruleBit# :: Int -> Int#
              ruleBit# 0 = 0# 
              ruleBit# _ = let (I# w1#) = w1 in w1#
              fill !cnt# !arrIdx !rule !ruleMask
                | cnt# ==# 0# = {-# CORE "fill_0" #-} {-# SCC "fill_0" #-} do
                    let (# n#, _ #) = fillS (leftOver# -# width# -# 1#) rule
                                                      ruleMask 0 (unsafeAt row arrIdx) (unsafeAt row lower)
                        -- shift final accumulated value and mask off any extraneous
                        -- bits at the top
                        newVal = ((I# n#) `unsafeShiftR` (intSize - leftOver)) .&. (2 ^ leftOver - 1)
                    unsafeWrite arr arrIdx newVal
                | otherwise = {-# CORE "fill_1" #-} {-# SCC "fill_1" #-} do
                    let (# newVal#, newRuleIdx# #) = fillS (intSize# -# width# -# 1#) rule
                                                  ruleMask 0 (unsafeAt row arrIdx) (unsafeAt row (arrIdx + 1))
                    unsafeWrite arr arrIdx (I# newVal#)
                    fill (cnt# -# 1#) (arrIdx + 1) (I# newRuleIdx#) ruleStartMask
              fillS !cnt# !rule !cellMask !val !currVal !nextVal
                  | cnt# ==# 0# = 
                      let newRuleIdx = ((rule .|. ruleBit (nextVal .&. 1)) `unsafeShiftR` 1) .&. ruleShiftMask
                          newVal = ((val `unsafeShiftR` 1) .&. h1) .|. unsafeAt rules rule
                      in {-# CORE "fillS_0" #-} {-# SCC "fillS_0" #-} fillE (width# -# 1#) newRuleIdx 2 newVal nextVal
                  | otherwise = 
                      let newRuleIdx = {-# SCC "fillS_12" #-} ((rule .|. (I# bit#)) `unsafeShiftR` 1) .&. ruleShiftMask
                          bit# = ruleBit# (currVal .&. cellMask)
                          newVal = ((val `unsafeShiftR` 1) .&. h1) .|. unsafeAt rules rule
                      in {-# CORE "fillS_1" #-} {-# SCC "fillS_1" #-} fillS (cnt# -# 1#) newRuleIdx (cellMask `unsafeShiftL` 1) newVal currVal nextVal
              fillE !cnt# !rule !cellMask !val !currVal 
                  | cnt# ==# 0# = 
                          let (I# newVal#) = newVal
                              (I# newRuleIdx#) = newRuleIdx
                          in {-# CORE "fillE_0" #-} {-# SCC "fillE_0" #-} (# newVal#, newRuleIdx# #)
                  | otherwise = {-# CORE "fillE_1" #-} {-# SCC "fillE_1" #-} fillE (cnt# -# 1#) newRuleIdx (cellMask `unsafeShiftL` 1) newVal currVal
                where
                  newVal = ((val `unsafeShiftR` 1) .&. h1) .|. (unsafeAt rules rule) 
                  newRuleIdx = ((rule .|. ruleBit (currVal .&. cellMask)) `unsafeShiftR` 1) .&. ruleShiftMask
            fill upper# 0 firstRule ruleStartMask
            return $! arr
