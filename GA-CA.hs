-- |
-- Module      : Main
-- Copyright   : Justin Bailey
-- License     : BSD3
--  
-- A program which 'evolves' cellular automata that can solve the 'majority'
-- classification problem.

-- Original author: Justin Bailey (jgbailey at gmail.com)

module Main

where

import CA
import Control.Monad (replicateM, unless)
import System.Random (randomRIO)
import Data.List (sortBy)
import Data.Array.IArray (Array,listArray, (!))
import Data.Time (getCurrentTime, diffUTCTime, UTCTime)
import Debug.Trace (trace)
import Control.Parallel.Strategies (parMap, rwhnf)

type Fitness = Float
type Classifier = (CA -> CA -> Int)
type Crossover = (Rule -> Rule -> IO Rule)
type Mutator = (Rule -> IO Rule)
type Breeder = [(Rule, Fitness)] -> IO [Rule]

main = do
    let numRules = 25
        numGenerations = 1
        ruleWidth = 3 -- Makes a 7 bit rule.
        numCAs = 25
        caWidth = 149 
        mutateProbability = 2
        crossOver = singlePointCrossOver 
        mutator = mutateWithProb mutateProbability
        iterations = caWidth * 2
        breedingPopulation = 9
        minFitness = 0.1
        classifier = classifyMajority -- allBlack
        ruleMaker = mkRandomRule ruleWidth -- return $ mkAllBlackRule ruleWidth
        caMaker = (replicateM numCAs (mkBiasedCA caWidth))
    start <- getCurrentTime
    putStrLn $ "Starting at: " ++ show start
    putStrLn $ show numGenerations ++ " generations, " ++
                show numRules ++ " " ++ show (ruleWidth * 2 + 1) ++
                " bit rules each, " ++ show numCAs ++ " initial CAs per rule."
    putStrLn $ "Gen.\tAvg.\tStd. Dev.\tMax."
    rules <- evolve numRules numGenerations iterations 
      classifier
      start
      ruleMaker
      caMaker
      (tournamentBreeder breedingPopulation minFitness crossOver) 
      mutator
    end <- getCurrentTime
    putStrLn "Top 10 rules"
    mapM_ (\(r, f) -> putStrLn $ "(" ++ show f ++ ") " ++ show r) (take 10 rules)
    putStrLn $ "Finished at: " ++ show end ++ ". Execution took " ++ (show $ diffUTCTime end start)
        
evolve :: Int -> Int -> Int -> Classifier -> UTCTime -> IO Rule -> IO [CA]
  -> Breeder -> Mutator -> IO [(Rule, Fitness)]
evolve ruleCnt numGen iterations classifier startTime mkRule mkCAs breeder mutator = evolve' startTime 1 []
  where
    evolve' start cnt prevRules =
          do
            putStr $ show cnt
            -- Sort results by their fitness
            results <- tournament iterations ruleCnt classifier prevRules mkRule mkCAs 
            putStr $ "\t" ++ show (mean (map snd results)) 
            putStr $ "\t" ++ show (stddev (map snd results))
            putStrLn $ "\t" ++ show (maximum (map snd results))
            if cnt == numGen
              then (return . sortBy fitness) results
              else
                do
                  newRules <- breeder results >>= mapM mutator 
                  end <- getCurrentTime
                  evolve' end (cnt + 1) newRules 
        where
          -- greatest to least
          fitness (_, f1) (_, f2) = compare f2 f1

-- From http://haskelldsp.sourceforge.net/Numeric/Statistics/Moment.hs
-- Thanks to Matthew Donadio (c) 

-- * Functions

-- | Compute the mean of a list
--
-- @Mean(X) = 1\/N sum(i=1..N) x_i @

-- We need to use Prelude.sum intead of sum because of a buglet in the
-- Data.List library that effects nhc98
mean :: (Fractional a) => [a] -> a
mean x = sum x / (fromIntegral . length) x

-- | Compute the variance of a list
--
-- @Var(X) = sigma^2@
--
-- @       = 1\/N-1 sum(i=1..N) (x_i-mu)^2 @

-- This is an approximation
-- var x = (mean $ map (^2) x) - mu^2
--    where mu = mean x

var :: (Fractional a) => [a] -> a
var xs = sum (map (\x -> (x - mu)^2) xs)  / (n - 1)
    where mu = mean xs
	  n = fromIntegral $ length $ xs

-- | Compute the standard deviation of a list
--
-- @ StdDev(X) = sigma = sqrt (Var(X)) @

stddev :: (RealFloat a) => [a] -> a
stddev x = sqrt $ var x

-- ^ If all cells are black, success. Otherwise, failure.
allBlack :: Classifier
allBlack initial final = if and (caBits final) then 1 else 0

alwaysWin :: Classifier
alwaysWin _ _  = 1

alwaysLose :: Classifier
alwaysLose _ _  = 0

-- ^ Takes initial and final CA row. Returns 1 if
-- the CA was classified correctly, zero otherwise.
classifyMajority :: Classifier
classifyMajority init final = 
  let (numInitWhite, numInitBlack) = (rowLength - numInitBlack, length (filter id (caBits init)))
      (numFinalWhite, numFinalBlack) = (rowLength - numFinalBlack, length (filter id (caBits final)))
      rowLength = caWidth init
      -- Return number of white (Zero) and black (One) cells in the row. Rowlength is a
      -- constant during the round, so number of black cells is the number of
      -- cells that weren't white.
      result =
        if numInitWhite > numInitBlack && (not (or (caBits final))) ||
            numInitBlack > numInitWhite && (and (caBits final))
          then 1
          else 0
  in result

classifyMost :: Classifier
classifyMost init final = 
  let (numInitWhite, numInitBlack) = (rowLength - numInitBlack, length (filter id (caBits init)))
      (numFinalWhite, numFinalBlack) = (rowLength - numFinalBlack, length (filter id (caBits final)))
      rowLength = caWidth init
      -- Return number of white (Zero) and black (One) cells in the row. Rowlength is a
      -- constant during the round, so number of black cells is the number of
      -- cells that weren't white.
      result =
        if numInitWhite > numInitBlack && numFinalWhite > numFinalBlack ||
          numInitBlack > numInitWhite && numFinalBlack > numFinalWhite
          then 1
          else 0
  in result 

noCrossOver :: Crossover
noCrossOver rule1 = return . (const rule1)

noMutation :: a -> IO a
noMutation = return . id

-- Mutate each bit according to probabity given. Argument should
-- be between 0 and 100.
mutateWithProb :: Int -> Mutator
mutateWithProb prob rule =
    do
      newBits <- mapM mutate' (ruleBits rule)
      let newRule = fromRule rule newBits
      -- putStrLn $ "Mutated " ++ show rule ++ " to " ++ show newRule
      return $! newRule
  where
    mutate' b =
      do
        i <- randomRIO (0, 99)
        return $! if i < prob
          then (not b)
          else b
          
singlePointCrossOver :: Crossover
singlePointCrossOver rule1 rule2 =
  do
    let ruleLen = ruleLength rule1 
    idx <- randomRIO (0, ruleLen - 1)
    let b1 = ruleBits rule1
        b2 = ruleBits rule2
        newRule = fromRule rule1 (take idx b1 ++ (drop idx b2))
    --putStrLn $ "Crossing " ++ show rule1 ++ " and " ++ show rule2 ++ " at " ++ show idx ++ " to get " ++ show newRule
    return $! newRule
  
-- Breed a list of rules based on the crossover function given. Each rule
-- gets to breed with breedingPop partners. Partners are probabilistically,
-- based on fitness.
tournamentBreeder :: Int -> Fitness -> Crossover -> Breeder
tournamentBreeder breedingPop minFitness crossover rules =
    -- If no rules are eligible or only one is elegible, return.
    -- Otherwise, breed.
    if null eligibleRules 
      then return []
      else
        if null (tail eligibleRules)
          then return $! map fst eligibleRules
          else mapM breed' (zip eligibleRules [0..])
  where
    eligibleRules = filter ((> minFitness) . snd) rules
    numRules = length eligibleRules
    -- Probabilistically select a mate for each rule and breed. Sometimes
    -- a rule may not breed and returns unchanged.
    breed' ((rule, fit), selfIdx) = do
    -- Pick a mate who isn't me
      let pickMate self = do
            n <- randomRIO (0, numRules - 1)
            if n == self
              then (pickMate self)
              else (return n)
      mateIndices <- sequence $ replicate breedingPop (pickMate selfIdx)
      let ruleArr :: Array Int (Rule, Fitness)
          ruleArr = listArray (0, numRules - 1) eligibleRules
          mates = (sortBy fitness . map (ruleArr !)) mateIndices
          fitnessRange = sum (map snd mates)
      -- Pick a random number to select mate by
      p <- randomRIO (0, fitnessRange)
      -- p will be between 0 and fitnessRange. Find mate by ordering by probability (greatest to least),
      -- then drop mates until sum of fitness' is greater than or equal to p. The last mate in the list
      -- will always be picked if nothing else.
      let mate = (fst . fst . head . dropWhile ((p >) . snd) . drop 1 . scanl (\(_, fit) m -> (m, fit + (snd m))) ((undefined, undefined), 0)) mates
      crossover rule mate
    -- highest to lowest
    fitness (_, f1) (_, f2) = compare f2 f1
    
-- Run each rule on the automatas given. Return a fitness score for each
tournament :: Int -> Int -> Classifier -> [Rule] -> IO Rule -> IO [CA] -> IO [(Rule, Fitness)]
tournament iterations cnt classifier prevRules mkRule mkCAs = do
    -- Make initial CAs
    initial <- mkCAs
    -- Make random rules.
    rules <- replicateM (cnt - length prevRules) mkRule >>= return .  (prevRules ++)
    return $! (zip rules (parMap rwhnf (caRound initial) rules))
  where    
    -- Determine how many automatas the rule is able to correctly classify. The
    -- value returned is the number of correctly classified automata out of
    -- all automata given.
    caRound :: [CA] -> Rule -> Fitness
    caRound initials rule = -- trace ("Top: " ++ show top ++ ", bot " ++ show bot ++ ", total " ++ show total)
        total
      where
        bot = (fromIntegral $ length initials)
        top = (fromIntegral $ sum (map (uncurry classifier) results))
        total = (top / bot)
        -- results = parMap rwhnf (\initRow -> (initRow, (head . drop (iterations + 1) . sim rule) initRow)) initials
        results = map (\initRow -> (initRow, (head . drop (iterations + 1) . sim rule) initRow)) initials
