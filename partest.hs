import Control.Parallel
import Control.Monad
import Text.Printf

fib :: Int -> Int
fib 0 = 0
fib 1 = 1
fib n = r `par` (l `pseq` l+r)
  where
    l = fib (n-1)
    r = fib (n-2)

main = forM_ [0 .. 45] $ \i ->
          printf "n=%d => %d\n" i (fib i)