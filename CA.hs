{-# LANGUAGE BangPatterns, TemplateHaskell #-}
{-# OPTIONS_GHC -fglasgow-exts #-}
-- |
-- Module      : CA
-- Copyright   : Justin Bailey
-- License     : BSD3
--  
-- Implements a cellular automata representation, and the ability to update the
-- automate based on a rule. 

-- Original author: Justin Bailey (jgbailey at gmail.com)

module CA (Rule, fromRule, ruleLength, CA, mkRule, sim, mkRandomRule, mkBiasedCA,
  mkAllWhiteRule, mkAllBlackRule, mkRandomCA, ruleBits, caBits, caWidth,
  mkWhiteCA, readRule)

where

import Ring
import System.Random (randomRIO)
import Control.Monad (replicateM)
import Control.Monad.ST.Strict (unsafeIOToST)
import Data.List (intersperse)
import Data.Array.Base (unsafeAt, unsafeWrite, unsafeRead, unsafeThawSTUArray, UArray(..))
import Data.Array.Unboxed (UArray)
import qualified Data.Array.Unboxed as UArray (listArray)
import Data.Array.IArray (elems, assocs, bounds)
import Data.Array.MArray (MArray)
import GHC.ST (ST)
import qualified Data.Array.ST as ST (runSTUArray, newListArray, writeArray, newArray_, STUArray, newArray, getAssocs)
import Data.Bits ((.&.), shiftL, (.|.), bitSize, testBit, clearBit, setBit, Bits(), shiftR, rotateL, shiftL, complement)
import Test.QuickCheck
import Data.Maybe (catMaybes)
import GHC.Base (int2Word#, word2Int#, Int(..), indexWordArray#, or#, and#, uncheckedShiftRL#, uncheckedShiftL#,
  (-#), (==#), (+#), ByteArray#, Word#, Int#, eqWord#, minusWord#)
import Debug.Trace
import GHC.Word (Word(..))

type CA = Ring 

data Rule = Rule { ruleWidth :: !Int, rules :: !(UArray Int Int) }

instance Show Rule where
  show = showSimpleRule

-- | Create a rule, assuming the given bit width. The width specifies the number
-- of bits to either side of a cell in which to look. A width of 2 implies
-- that 5 bits will be examined, so 32 rules are need. A width of 3 implies
-- 7 bits, requiring 128 rules.
-- Therefore the association list should have at least 2 ^ (width * 2 + 1) mappings from integers
-- to bit values.
--
-- When a rule is applied, the automata cells are converted
-- to an integer value, which is used to look up the corresponding color in
-- the rule table.
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

-- | Reads a rule consiting of 1's and 0's. Any other characters are ignored.
-- A newline terminates the rule. The width of the rule is determined by the
-- length of the string. The rule is rounded down to the closest width
readRule :: String -> Rule
readRule s = mkRule neighbors bits
  where
    bits = catMaybes $ map toBool s
    neighbors = max 1 (((floor $ log bitLength / log 2) - 1) `div` 2)
    bitLength = fromIntegral $ length bits
    toBool '0' = Just False
    toBool '1' = Just True
    toBool _ = Nothing

-- | Create a rule with new bits from an existing rule.
fromRule :: Rule -> [Bool] -> Rule
fromRule (Rule w _) = mkRule w

-- | Gets the bit patterns for this rule. The bits are arranged in ascending
-- order according to the value of the keys given. The pattern for each
-- bit is therefore implicit in the position of the bit.
ruleBits :: Rule -> [Bool]
ruleBits = map toBool . elems . rules

toBool :: Int -> Bool
toBool 0 = False
toBool _ = True

-- ^ Number of bits that make up this rule. 
ruleLength :: Rule -> Int
ruleLength (Rule w _) = 2 ^ (w * 2 + 1)

-- ^ Width of the automata.
caWidth :: CA -> Int
caWidth = size

-- ^ Bits that make up an automata.
caBits :: CA -> [Bool]
caBits = toListR

h1 :: Int
h1 = $([|clearBit (complement 0) ((bitSize (undefined :: Int)) - 1)|]) -- 2147483647 

intSize :: Int
intSize = $([|bitSize (undefined :: Int)|]) -- 32 

-- ^ Simulate the CA infinitely, using the rule given. Return the final CA. Note that rules
-- are matched left to right. That is, when neighboring cells are examined
-- to match a rule, they are read left to right and the most significant
-- bit is on the left.
sim :: Rule -> CA -> [CA]
sim = simWithUArray stepWithUArray

-- | Make a CA that is biased to white or black, randomly. CAs should
-- have 75% white or black bits.
mkBiasedCA :: Int -> IO CA
mkBiasedCA width  =
    do
      -- Randomly determine if we are biased towards white or black
      bias <- randomRIO (0 :: Int, 1) >>= return . (== 0)
      let selectVal n
            | n >= 75 && bias = True -- Biased to white
            | bias = False
            | n >= 75 && not bias = False -- Biased to black
            | otherwise = True
      vals <- replicateM width (randomRIO (0 :: Int, 99) >>= return . selectVal)
      return $! fromListR vals

-- ^ Make a random CA row with the given width.
mkRandomCA :: Int -> IO CA
mkRandomCA width  =
  do
    vals <- replicateM width (randomRIO (0 :: Int, 1) >>= \n -> return $ if n == (0 :: Int) then False else True)
    return $! fromListR vals

-- ^ Make an all white CA.
mkWhiteCA :: Int -> IO CA
mkWhiteCA width = return $! (fromListR (replicate width False))

-- | Makes a random rule with the given number of neighbors on each side of the
-- cell. The rule has full coverage of all possible configurations. 
mkRandomRule :: Int -> IO Rule
mkRandomRule neighbors =
  do
    rules <- replicateM (2 ^ (neighbors * 2 + 1)) (randomRIO (0 :: Int, 1) >>= \n -> return $ if n == (0 :: Int) then False else True)
    return $! mkRule neighbors rules

-- | Make a rule that turns all cells white.
mkAllWhiteRule :: Int -> Rule
mkAllWhiteRule w = mkRule w (repeat False)

-- | Make a rule that turns all cells black.
mkAllBlackRule :: Int -> Rule
mkAllBlackRule w = mkRule w (repeat True)

showSimpleRule (Rule w r) = "[" ++ concatMap showBit (elems r) ++ "]"
    where
      showBit 0 = "0"
      showBit _ = "1"

showFullRule (Rule w r) = show w ++ " [" ++ concat (intersperse ", " $ map showBit (assocs r)) ++ "]"
    where
      showBit (i, b) = "(" ++ show i ++ "," ++ show b ++ ")"

-- | Advance the CA one step, using the
-- rule given. The automata is examined from left to right. The same
-- cell which was current when step began will be current when the step
-- ends. This function is kept around to verify the stepWithUArray function.
stepSimple :: Int -> Rule -> CA -> CA
stepSimple rowLen rule@(Rule width rules) row =
  -- Apply rule to each cell in CA. 
  let getRule currIdx = pattern' start 0
        where
          start = (currIdx + width)
          end = (currIdx - width)
          -- Move left to right, determine rule to retrieve.
          pattern' cnt !result
            | cnt < end = result
            | otherwise = if (currR cnt row)
                            then pattern' (cnt - 1) (result * 2 + 1)
                            else pattern' (cnt - 1) (result * 2)
      cells = map (toBool . unsafeAt rules . getRule) [0 .. rowLen - 1]
      result = fromUArray (UArray.listArray (0, rowLen - 1) cells)
  in -- trace ("retrieved rules: " ++ show (map getRule [0 .. rowLen - 1])) 
         result

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

-- | Simulate using the step function. Kept to verify results against simWithUArray.  
simSimple rule initial = go (stepSimple (caWidth initial) rule) initial
  where
    go f !v = v : go f (f v)

simWithUArray :: (Rule -> Int -> UArray Int Int -> UArray Int Int) -> Rule ->  CA -> [CA]
simWithUArray step rule initial =
    if (ruleWidth rule) < leftOver
      then map toRing . go (step rule leftOver) $ vals
      else error $ "Rule width must be less than left over in CA (" ++ show leftOver ++ " in this case)."
  where
    -- Take array of integers an convert back to ring of bools.
    toRing = fromListR . take (caWidth initial) . concatMap bitsToBool . elems 
      where
        -- Builds from left to right, least significant to most significant.
        bitsToBool :: Int -> [Bool]
        bitsToBool val = bitsToBool' val intSize
          where
            bitsToBool' _ 0 = []
            bitsToBool' val cnt = bitVal val : bitsToBool' (val `shiftR` 1) (cnt - 1)
            bitVal val
              | val .&. 1 == 1 = True
              | otherwise = False
    -- iterate with a strict result
    go f !v = v : go f (f v)
    (vals, leftOver) = arrToBits (toUArray initial)
    -- Convert list of booleans to bits in integers (stored in an array). Also
    -- return the "left over" bits in the last element of the array. The left
    -- over bits must greater than the width of the rule.
    arrToBits :: (UArray Int Bool) -> (UArray Int Int, Int)
    arrToBits elems = ((ST.runSTUArray arr), leftOver)
      where (lower, upper) = bounds elems
            width = (upper - lower) + 1
            leftOver = width `rem` intSize -- can be as high as 31
            arr :: ST s (ST.STUArray s Int Int)
            arr = 
              (do
                let amt = width `div` intSize
                arr <- ST.newArray_ (0, if leftOver == 0 then (amt - 1) else amt) :: ST s (ST.STUArray s Int Int)
                let fill idx last bIdx
                      | bIdx > upper = do
                          let arrIdx = idx `div` intSize
                          unsafeWrite arr arrIdx last
                      | otherwise = do
                          let arrIdx = idx `div` intSize
                              pos = idx `rem` intSize
                              e = unsafeAt elems bIdx
                          let val' = if e then setBit last pos else clearBit last pos
                          if pos == intSize - 1
                            then do
                              unsafeWrite arr arrIdx val'
                              fill (idx + 1) 0 (bIdx + 1)
                            else
                              fill (idx + 1) val' (bIdx + 1) 
                fill 0 0 0
                return $! arr)

-- ^ Bits from left to right                      
showBits :: (Bits a) => a -> String
showBits n = concatMap (\i -> if testBit n i then "1" else "0") [0..bitSize n - 1]

newtype RuleX = RuleX Rule
  deriving Show
  
instance Arbitrary RuleX where
  arbitrary = do
    width <- choose (1, 3) :: Gen Int
    rules <- vector (2 ^ (2 * width + 1)) :: Gen [Bool]
    return $! RuleX (mkRule width rules)
  coarbitrary = undefined

newtype CellX = CellX CA
  deriving Show
  
instance Arbitrary CellX where
  arbitrary = do
    cellSize <- choose (20, 200) :: Gen Int
    cells <- vector cellSize :: Gen [Bool]
    return $! CellX (fromListR cells)
  coarbitrary = undefined

prop_compare_steps :: RuleX -> CellX -> Property
prop_compare_steps (RuleX rule) (CellX ca) =
    let stepsU = simWithUArray stepWithUArray rule ca
        stepsS = simSimple rule ca
    in
      (ruleWidth rule) < (caWidth ca `rem` intSize) ==>
      and (zipWith (\ca1 ca2 -> and (zipWith (==) (toListR ca1) (toListR ca2))) (take 2 stepsU) (take 2 stepsS))
