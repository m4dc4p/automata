{-# OPTIONS_GHC -fbang-patterns -fglasgow-exts -O2 -fexcess-precision -funbox-strict-fields #-}
-- |
-- Module      : Test.hs
-- Copyright   : Justin Bailey
-- License     : BSD3
--  
-- Implements a cellular automata representation, and the ability to update the
-- automate based on a rule.
-- Compile with GHC 6.8.1.
--
-- Original author: Justin Bailey (jgbailey at gmail.com)

import qualified Data.Array.Unboxed as UArray (listArray)
import System.Random (randomRs, newStdGen)
import Data.Array.Base (unsafeAt, unsafeWrite, UArray(..))
import Data.Array.IArray (elems, bounds)
import Data.Bits ((.&.), shiftL, (.|.), bitSize, testBit, clearBit, setBit, Bits(), shiftR, shiftL, complement)
import qualified Data.Array.ST as ST (runSTUArray, newListArray, newArray_, STUArray)
import GHC.ST (ST)
import GHC.Base (int2Word#, word2Int#, Int(..), indexWordArray#, or#, and#, uncheckedShiftRL#, uncheckedShiftL#,
  (-#), (==#), (+#), ByteArray#, Word#, Int#, eqWord#, minusWord#)
import Control.Monad (when)

data Rule = Rule { ruleWidth :: Int, rules :: UArray Int Int }

main = do
  gen <- newStdGen
  let neighbors = 1
      width = 80
      leftOver = width `mod` intSize
      arrSize = width `div` intSize
v v v v v v v
      row = take arrSize $ randomRs (minBound :: Int, maxBound :: Int) gen
  rule <- return mkRule110
  when (arrSize == 0) (error "Array cannot be zero length.")
  let result = iterate (stepWithUArray rule leftOver) $ UArray.listArray (0, arrSize) row
*************
  -- Make a rule that turns all cells black
  rule <- mkRandomRule neighbors
  -- make some random numbers up and stick in array
  row <- replicateM arrSize (randomRIO (minBound :: Int, maxBound :: Int))
  -- Automata is 149 cells wide. Set leftover bits appropriately. Note this depends
  -- on 32 bit architecture.
  let result = take 100000 $ iterate (stepWithUArray rule leftOver) (UArray.listArray (0, arrSize) row)
^ ^ ^ ^ ^ ^ ^
  -- Show steps.
  mapM_ (\(i, r) -> putStrLn . ((show i ++ "] ")   ++) . take width . (concatMap showBits) . elems $ r) $ zip [1..] result

mkRule110 = mkRule 1 [False, True, True, True, False, True, True, False]
  
-- | Makes a random rule with the given number of neighbors on each side of the
-- cell. The rule has full coverage of all possible configurations. 
mkRandomRule :: Int -> IO Rule
mkRandomRule neighbors =
  do
    gen <- newStdGen
    let rules = take (2 ^ (neighbors * 2 + 1)) . map  (/= 0) $ randomRs (0 :: Int, 1) gen
    return $! mkRule neighbors rules

mkRule :: Int -> [Bool] -> Rule
mkRule w rules = Rule w arr
  where
    arr :: UArray Int Int
    arr = ST.runSTUArray 
      (do
        ST.newListArray (0, (2 ^ (w * 2 + 1) - 1)) (map toHighBit rules))
    -- -^ Value with all bits as zero except highest. This value is used in the rules array
    -- to directly mask the result of the rule onto the accumulating
    -- integer in stepWithBitRing
    toHighBit True = setBit 0 ((bitSize (undefined :: Int)) - 1)
    toHighBit _ = 0

-- | This step function works with the cellular automata represented as
-- an array of integers. Because of specific optimizations in the function,
-- it requires that the cellular automata width `mod` integer size be greater
-- than the rule width. 
stepWithUArray :: Rule -> Int -> UArray Int Int -> UArray Int Int
stepWithUArray rule@(Rule !width !rules) !leftOver !row =
    ST.runSTUArray fillRow
  -- Apply rule to each cell in CA. 
  where
      (lower, upper) = bounds row
      w2 :: Int
      w2 = 2 ^ (width + 1)
      leftOverMask = 2 ^ leftOver - 1
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
      toWord# (I# i#) = i2w# i#
      i2w# = int2Word#
      w2i# = word2Int#
      ruleBit# v#
        | (i2w# 0#) `eqWord#` v# = i2w# 0#
        | otherwise = w1#
      -- Constants converted to unlifted words or ints
      h1# = toWord# (clearBit (complement 0) ((bitSize (undefined :: Int)) - 1))
      w1# = toWord# (2 ^ (width * 2 + 1))
      ruleStartMask# = toWord# w2
      ruleShiftMask# = w1# `minusWord#` (i2w# 1#)
      firstRule# = toWord# firstRule
      (I# upper#) = upper
      (I# lower#) = lower
      (I# intSize#) = intSize
      (I# width#) = width
      (I# leftOver#) = leftOver
      (UArray _ _ _ row#) = row
      (UArray _ _ _ rules#) = rules
      leftOverMask# = toWord# leftOverMask
      fillRow :: forall s. ST s (ST.STUArray s Int Int)
      fillRow = {-# SCC "step_fillRow" #-}
          do
            arr <- ST.newArray_ (lower,upper)
            let
              -- Return value which, when masked to ruleIdx, will allow
              -- ruleIdx to be shifted right one place and then have the correct value.
              fill !cnt# !arrIdx# !rule# !ruleMask#
                | cnt# ==# 0# = {-# SCC "fill_0" #-} do
                    let (# n#, _ #) = fillS (leftOver# -# width# -# 1#) rule#
                                                      ruleMask# (i2w# 0#) (indexWordArray# row# arrIdx#) (indexWordArray# row# lower#)
                        -- shift final accumulated value and mask off any extraneous
                        -- bits at the top
                        newVal# = (n# `uncheckedShiftRL#` (intSize# -# leftOver#)) `and#` leftOverMask#
                    unsafeWrite arr (I# arrIdx#) (I# (w2i# newVal#))
                | otherwise = {-# SCC "fill_1" #-} do
                    let (# newVal#, newRuleIdx# #) = fillS (intSize# -# width# -# 1#) rule#
                                                  ruleMask# (i2w# 0#) (indexWordArray# row# arrIdx#) (indexWordArray# row# (arrIdx# +# 1#))
                    unsafeWrite arr (I# arrIdx#) (I# (w2i# newVal#))
                    fill (cnt# -# 1#) (arrIdx# +# 1#) newRuleIdx# ruleStartMask#
              fillS !cnt# !rule# !cellMask# !val# !currVal# !nextVal#
                  | cnt# ==# 0# = {-# SCC "fillS_0" #-}
                      let newRuleIdx# = ((rule# `or#` ruleBit# (nextVal# `and#` (i2w# 1#))) `uncheckedShiftRL#` 1#) `and#` ruleShiftMask#
                      in fillE (width# -# 1#) newRuleIdx# (i2w# 2#) newVal# nextVal#
                  | otherwise = {-# CORE "fillS_1" #-} {-# SCC "fillS_1" #-}
                      let newRuleIdx# = ((rule# `or#` ruleBit# (currVal# `and#` cellMask#)) `uncheckedShiftRL#` 1#) `and#` ruleShiftMask#
                      in fillS (cnt# -# 1#) newRuleIdx# (cellMask# `uncheckedShiftL#` 1#) newVal# currVal# nextVal#
                where
                  newVal# = ((val# `uncheckedShiftRL#` 1#) `and#` h1#) `or#` (indexWordArray# rules# (w2i# rule#))
              fillE !cnt# !rule# !cellMask# !val# !currVal# 
                  | cnt# ==# 0# = {-# SCC "fillE_0" #-} (# newVal#, newRuleIdx# #)
                  | otherwise = {-# SCC "fillE_1" #-} fillE (cnt# -# 1#) newRuleIdx# (cellMask# `uncheckedShiftL#` 1#) newVal# currVal#
                where
                  newVal# = ((val# `uncheckedShiftRL#` 1#) `and#` h1#) `or#` (indexWordArray# rules# (w2i# rule#))
                  newRuleIdx# = ((rule# `or#` ruleBit# (currVal# `and#` cellMask#)) `uncheckedShiftRL#` 1#) `and#` ruleShiftMask#
            fill upper# 0# firstRule# ruleStartMask#
            putStrLn $ "Filled!"
            return $! arr

-- ^ Bits from left to right                      
showBits :: (Bits a) => a -> String
showBits n = concatMap (\i -> if testBit n i then "1" else "0") [0..bitSize n - 1]
    
intSize :: Int
intSize = bitSize (undefined :: Int)
