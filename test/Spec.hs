module Spec where

import ShortStuff

main :: IO ()
main = do
  let res = zAlgorithm "aaaabaaaa" "aab"
  putStrLn $ "Result: " ++ show res
  -- some <- return 1
  -- putStrLn $ "Test suite not yet implemented" ++ show some
