import System.Environment (getArgs)
import Data.List (genericDrop)

dropTest :: Integer -> Integer
dropTest n = head . genericDrop n $ [1..]

main = do
  n <- getArgs >>= return . read . head
  putStrLn $ show $ dropTest n