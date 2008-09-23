{-# LANGUAGE BangPatterns #-}
-- |
-- Module      : Ring
-- Copyright   : Justin Bailey
-- License     : BSD3
--  
-- Implements a ring buffer. THe buffer is write-once, read-only. 

-- Original author: Justin Bailey (jgbailey at gmail.com)

module Ring (Ring, current, rotR, rotL, toListL, toListR, fromListL,
              fromListR, size, currR, currL, fromUArray, foldl1', toUArray)

where

import Data.List (foldl')
-- For testing
import Test.QuickCheck
import Control.Monad (replicateM_, replicateM)
import System.Random (randomRIO)
import System.Environment (getArgs)
import Data.Foldable (Foldable(..))
import Data.Monoid (mappend, mempty)
import qualified Data.Foldable as F (foldl, foldl1, foldr)
import Data.Array.Base (unsafeAt)
import Data.Array.ST as ST (runSTUArray, newListArray, STUArray, runSTArray, newArray_, writeArray)
import GHC.ST (ST)
import Data.Array.Unboxed (IArray, UArray, assocs, bounds, (!))
import Data.Array.MArray (MArray)

-- | A ring is a sequence with a current value. The left end of the sequence
-- is to the 'right' of the current value. The right end of the sequence
-- is to the 'left' of the current value.
data Ring = Ring { currIdx :: !Int, vals :: (UArray Int Bool), lower, upper, size:: !Int }

instance Show Ring where
  show (Ring idx arr _ _ _) = "{" ++ concatMap showElem (assocs arr) ++ "}"
    where
      showElem (i, e) =
        if i == idx
          then "[" ++ showBool e ++ "]"
          else showBool e
      showBool True = "1"
      showBool False = "0"

-- | Build a ring from a list. The first element in the list
-- will be the current element when the ring is built. The rest
-- of the list will be to the left of the current element.
-- fromListL :: (IArray UArray a) => [a] -> Ring a
fromListL :: [Bool] -> Ring 
fromListL [] = error "fromListL: Can't create empty ring"
fromListL ls = Ring upper arr lower upper (upper + 1)
  where
    (lower, upper) = (0, length ls - 1)
    arr = ST.runSTUArray (ST.newListArray (0, upper) (reverse ls))


-- ^ Build a ring from a list. The first element in the list
-- will be the current element when the ring is built. The rest
-- of the list will be to the right of the current element.
fromListR :: [Bool] -> Ring 
fromListR [] = error "fromListR: Can't create empty ring"
fromListR ls = Ring 0 arr lower upper (upper + 1)
  where
    (lower, upper) = (0, length ls - 1)
    arr = ST.runSTUArray (ST.newListArray (lower, upper) ls)

fromUArray :: (UArray Int Bool) -> Ring
fromUArray arr = Ring 0 arr lower upper (upper + 1)
  where
    (lower, upper) = bounds arr
    
-- ^ Creates a list by moving left along ring from current element.
-- That is, the list is built counter-clockwise. The current element
-- becomes the head of the list, and the last element is the one
-- to the right of the current. The following relationship holds:
--
-- (toListL . fromListR) ls = ls
--
toListL (Ring curr arr l u _) = map (unsafeAt arr) ([curr .. u] ++ [l .. curr - 1])

-- ^ Creates a list by moving right along ring from current element.
-- That is, the list is built clockwise. The current element becomes
-- the head of the list and the last is the one to the left of the
-- current. The following relationship holds:
--
-- (toListR . fromListL) ls = ls
--
toListR (Ring curr arr l u _) =
  let currToLower idx
        | idx == (l - 1) = []
        | otherwise = idx : currToLower (idx - 1)
      upperToCurr idx
        | idx == curr = []
        | otherwise = idx : upperToCurr (idx - 1)
  in map (unsafeAt arr) (currToLower curr ++ upperToCurr u)

-- | Return the UArray associated with the ring. Does not look
-- at currrent position.
toUArray (Ring _ arr _ _ _) = arr

-- | The current element of the ring.    
current (Ring curr arr _ _ _) = unsafeAt arr curr

-- ^ Get element to the right of current by given amount.
currR :: Int -> Ring -> Bool
currR amt r@(Ring curr arr l u s) = {-# SCC "currR_unsafeAt" #-} unsafeAt arr ((curr + amt) `mod` s)

-- ^ Get element to the left of current by given amount.
currL :: Int -> Ring -> Bool
currL amt r@(Ring curr arr l u s) = unsafeAt arr ((curr - amt) `mod` s)
    
-- ^ Rotate the ring right (clockwise) n steps, so the current element
-- becomes the one to the *left* n steps. 
rotR amt r
    | amt == 0 = r
    | amt > 0 = goRight r rotAmt
    | otherwise = goLeft r rotAmt
  where
    rotAmt = (abs amt) `mod` (size r)

-- ^ Rotate the ring left (counter-clockwise) n steps, so the current element
-- becomes the one to the *right* n steps. 
rotL amt r
    | amt == 0 = r
    | amt > 0 = goLeft r rotAmt
    | otherwise = goRight r rotAmt
  where
    rotAmt = (abs amt) `mod` (size r)

goRight ring@(Ring curr _ l u _) steps =
  let goRight' idx amt  
        | amt == 0 = ring { currIdx = idx }
        | otherwise =
            if idx == u
              then goRight' l (amt - 1)
              else goRight' (idx + 1) (amt - 1)
  in goRight' curr steps


goLeft ring@(Ring curr _ l u _) steps =
  let goLeft' idx amt
        | amt == 0 = ring { currIdx = idx }
        | otherwise =
            if idx == l
              then goLeft' u (amt - 1)
              else goLeft' (idx - 1) (amt - 1)
  in goLeft' curr steps

-- ^ Fold over the ring from left to right, strictly. 
foldl1' :: (Int -> Bool -> Bool) -> Ring -> Ring
foldl1' f (Ring curr arr l u s) = Ring curr (ST.runSTUArray createArray) l u s
  where
    valAt idx = unsafeAt arr idx
    createArray :: ST s (STUArray s Int Bool)
    createArray =
      do
        arr <- ST.newArray_ (l, u) 
        let foldl1_ !idx !cnt !val
              | cnt > s = return ()
              | otherwise = do
                  ST.writeArray arr idx val
                  let next = if idx == u then l else (idx + 1)
                  foldl1_ next (cnt + 1) (f next (valAt next))
        foldl1_ curr 0 (f curr (valAt curr))
        return $! arr

-- Test that rotating right and left leaves ring unchanged      
prop_rotation_invertable :: Int -> [Bool] -> Property
prop_rotation_invertable amt elems =
  let ring = (fromListL elems)
  in
    not (null elems) ==>
      (current ring) == (current (rotL amt (rotR amt ring)))

-- Test that a list comes out the same as it went in, if
-- no rotations are performed.
prop_list_unchanged :: [Bool] -> Property
prop_list_unchanged elems =
    not (null elems) ==>
      elems == (toListL . fromListR) elems &&
      elems == (toListR . fromListL) elems

-- Test that the list comes out the same after being rotated
-- by the count of the list. Rotation direction doesn't matter.
prop_list_unchanged_by_rotation :: [Bool] -> Property
prop_list_unchanged_by_rotation elems =
  let listLen = length elems
  in
    not (null elems) ==>
      elems == (toListL . rotR listLen . fromListR) elems &&
      elems == (toListR . rotL listLen . fromListL) elems &&
      elems == (toListL . rotL listLen . fromListR) elems &&
        elems == (toListR . rotR listLen . fromListL) elems

prop_curr_positive_amounts :: [Bool] -> Property
prop_curr_positive_amounts elems =
  let ringR = fromListR elems
      ringL = fromListL elems
      listLen = length elems
      iterateCurrR curr i = currR i curr : iterateCurrR curr (i + 1)
      iterateCurrL curr i = currL i curr : iterateCurrL curr (i + 1)
  in
    not (null elems) ==>
      all (\(l, r) -> l == r) (take (listLen * 2) (zip (cycle elems) (iterateCurrR ringR 0))) &&
      all (\(l, r) -> l == r) (take (listLen * 2) (zip (cycle elems) (iterateCurrL ringL 0)))

prop_curr_any_index :: [Bool] -> Int -> Property
prop_curr_any_index elems idx =
  let ringR = fromListR elems
      ringL = fromListL elems
      listLen = length elems
  in
    not (null elems) ==>
      currR idx ringR == (elems !! (idx `mod` listLen)) &&
      currL idx ringL == (elems !! (idx `mod` listLen))
      
allTests = do
  quickCheck prop_rotation_invertable
  quickCheck prop_list_unchanged
  quickCheck prop_list_unchanged_by_rotation
  quickCheck prop_curr_positive_amounts
  quickCheck prop_curr_any_index

