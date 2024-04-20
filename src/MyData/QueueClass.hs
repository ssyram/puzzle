{-# LANGUAGE BangPatterns #-}
module MyData.QueueClass where
import Control.Monad.ST
import Control.Monad (when, forM_)
import Data.Maybe (isJust)

class STQueue q where
  new :: ST s (q s e)
  -- | Default implementation: dequeue and then enqueue, return the value gotten out
  front :: q s e -> ST s (Maybe e)
  front queue = do
    !hd <- dequeue queue
    forM_ hd $ enqueue queue
    return hd
  enqueue :: q s e -> e -> ST s ()
  dequeue :: q s e -> ST s (Maybe e)
  len :: (Num n) => q s e -> ST s n
  -- | Default implementation: length is `0`
  isEmpty :: q s e -> ST s Bool
  isEmpty queue = (== 0) <$> len queue
