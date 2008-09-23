{-# GHC_OPTIONS -fglasgow-exts #-}
import GHC.Base (int2Word#, word2Int#, Int(..), eqWord#)

main = putStrLn $ show $ I# (word2Int# (x (int2Word# 0#)))
  where
    x e | e `eqWord#` (int2Word# 0#) = (int2Word# 1#)



bar = fooA
  where
    fooA =
      let (# i #) = fooB 0
      in I# (word2Int# i)
    fooB i = (# int2Word# 0#  #)