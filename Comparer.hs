{-# OPTIONS_GHC -fbang-patterns #-}
import Data.List (tails)
import System.Environment (getArgs)
import Data.Time.Clock
import CA
import Ring (toListL, fromListR)

neighbours :: Int -> [a] -> [[a]]
neighbours w = rotL . take w . map (take 3) . tails . cycle

rotL :: [a] -> [a]
rotL xs = last xs : init xs

type SimpleRule a = [a] -> a

step :: Int -> SimpleRule a -> [a] -> [a]
step w f = map f . neighbours w

rule110 :: SimpleRule Char
rule110 "   " = ' '
rule110 "X  " = ' '
rule110 "XXX" = ' '
rule110 _     = 'X'

naive iterations initial = let f = step (length init) rule110
                               init = map (\n -> if n then 'X' else ' ') . toListL $ initial
       in do
        putStrLn $ show (neighbours (length init) init)
        putStrLn $ show . map (\c -> if c == 'X' then '1' else '0') . head . drop iterations . go f $ init
  where
    go f !v = v : go f (f v)

mkRule110 = mkRule 1 [False, True, True, True, False, True, True, False]

execSim iterations f initial = do
  putStrLn . show . head . drop iterations . f $ initial
  
lifted iterations initial = execSim iterations (simWithUArray stepWithUArrayOld mkRule110) initial

liftedWord iterations initial = execSim iterations (simWithUArray stepWithUArrayWord mkRule110) initial

unlifted iterations initial = execSim iterations (simWithUArray stepWithUArray mkRule110) initial

simple iterations initial = execSim iterations (simSimple mkRule110) initial

elapsedTime f = do
  startTime <- getCurrentTime
  result <- f 
  endTime <- getCurrentTime
  putStrLn $ "Execution took " ++ show (diffUTCTime endTime startTime)
  
main = do
  iterations <- getArgs >>= return . read . head 
  putStrLn $ "Doing " ++ show iterations  ++ " iterations."

  initial <- mkRandomCA 80
  putStrLn $ "Starting with\n" ++ show initial
  
  putStrLn "Unlifted"
  elapsedTime $ unlifted iterations initial

{-  putStrLn "Lifted Word"
  elapsedTime $ liftedWord iterations initial-}

  putStrLn "Lifted"
  elapsedTime $ lifted iterations initial

{-  putStrLn "Simple"
  elapsedTime $ simple iterations initial

  putStrLn "Naive"
  elapsedTime $ naive iterations initial-}
