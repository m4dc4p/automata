module Util

where

import CA
import System.Random (randomRIO)
import Control.Monad (replicateM)
import Ring
import Data.Maybe (catMaybes)
import Data.Array.IArray (elems)

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
