{-# LANGUAGE ScopedTypeVariables #-}
module TrySBV where

import Data.SBV
import Data.SBV.Control
import Documentation.SBV.Examples.ProofTools.BMC (S(y))

class Prop p where
  (/\) :: p -> p -> p
  (\/) :: p -> p -> p

someTest :: Num a => a -> a
someTest x =
  let y = x in
  let y = -x in
  y



-- mainRun = runSMTWith z3 $ do
--   t <- sReal "t"
--   x <- forall "x"
--   let property = 2 .< x .&& x .< 3 .=> (t .>= 0 .&& t + x * t .<= 10)
--   constrain property
--   query qeResult

-- qeResult :: Query String
-- qeResult = do
--   -- Z3 command to perform quantifier elimination
--   cmd "(apply (using-params (then qe) :print-true))"
--   skipToNextCheckSat
--   extractModel

printMain :: IO ()
printMain = do
  result <- qeExample
  print result

-- >>> qeExample
qeExample :: IO ThmResult
qeExample = prove $ do
  t <- sReal "t"
  x <- forall "x"
  let property = 2 .< x .&& x .< 3 .=> (t .>= 0 .&& t + x * t .<= 10)
  return property
