{-# LANGUAGE Strict #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# LANGUAGE BangPatterns #-}
module Strict () where
import Control.Monad.Cont (MonadCont(callCC), forM_, MonadTrans (lift))
import Control.Monad.ST.Strict ( runST )
import Control.Monad (when)
import Utils ( Modifiable(readRef, newRef), (<<-) )
import Data.Functor.Identity (Identity(runIdentity))
import qualified Data.List as List

-- >>> fib 40 :: Int
-- 165580141
fib :: (Ord a, Num a, Num p) => a -> p
fib n
  | n <= 1    = 1
  | otherwise = fib (n - 1) + fib (n - 2)

-- >>> quickFib 40
-- 165580141
-- >>> quickFib 100
-- 573147844013817084101
quickFib :: (Ord a, Num b, Num a) => a -> b
quickFib n = fst $ getUntil n where
  getUntil :: (Ord a, Num b, Num a) => a -> (b, b)
  getUntil !n
    | n <= 1 = (1, 1)
    | otherwise =
      -- `m` stands for `minus`, so `nm1` is `n - 1` and `nm2` is `n - 2`
      let (!nm1, !nm2) = getUntil (n - 1) in
      (nm1 + nm2, nm1)

-- >>> stQuickFib 40
-- 165580141
-- >>> stQuickFib 100
-- 573147844013817084101
stQuickFib :: (Num a, Num p, Enum p) => p -> a
stQuickFib n = runST $ do
  c <- newRef 1
  f <- newRef 1
  forM_ [2..n] $ \_ -> do
    cVal <- readRef c
    lVal <- readRef f
    c <<- cVal + lVal
    f <<- cVal
  readRef c

-- >>> fibList !! 100
-- 573147844013817084101
fibList :: (Num a, Ord a) => [a]
fibList = nextList 1 1 where
  nextList !x !y = x : nextList y (x + y)

-- | `Word` is the non-negative type -- as one is asked to take out the index, which cannot be negative
-- prop> withMaxSuccess 10000 quickTestFibAndList
-- +++ OK, passed 10000 tests.
quickTestFibAndList :: Word -> Bool
quickTestFibAndList n =
  fibList `List.genericIndex` n == stQuickFib n &&
  fibList `List.genericIndex` n == quickFib n


