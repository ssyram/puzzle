{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
module MyData.LoopQueue 
(
  Queue,
  new,
  enqueue,
  dequeue,
  len,
  isEmpty,
  front
) 
where

import MyData.QueueClass

import Control.Monad.ST
import Data.Array.ST
import qualified MyData.Vector as Vec
import Data.STRef
import Utils
import Control.Monad (forM_, forM)

-- next should point to the next positition to be enqueued
data Queue s e = Queue {
  -- | Left () is the default value as a placeholder.
  --   This is to distinguish with `Maybe`, so to make the codes more readable
  valQueue :: !(STRef s (Vec.Vector s (Either () e))),
  frontPosQueue :: !(STRef s Integer),
  -- | The next position to put stuff inside -- should always represent an EMPTY place
  nextPosQueue :: !(STRef s Integer)
}

instance STQueue Queue where
  new :: ST s (Queue s e)
  new = do
    !val <- Vec.newWithSize (Left ()) 32
    !valQ <- newSTRef val
    !st <- newSTRef 0
    !next <- newSTRef 0
    return $ Queue valQ st next

  len :: (Num n) => Queue s e -> ST s n
  len q = do
    !len <- Vec.len =<< readSTRef (valQueue q)
    (!st, !next) <- getQueuePointers q
    let int = if next > st then next - st else next + len - st
    return $ fromInteger int

  isEmpty :: Queue s e -> ST s Bool
  isEmpty q = do
    (!st, !next) <- getQueuePointers q
    return $ st == next

  dequeue :: Queue s a -> ST s (Maybe a)
  dequeue q = do
    !isEmpty <- isEmpty q
    if isEmpty then return Nothing else do
      (!st, _) <- getQueuePointers q
      !vec <- readSTRef $ valQueue q
      ~(Just (Right !val)) <- Vec.readAt vec st
      writeSTRef (frontPosQueue q) $ st + 1
      return $ Just val

  front :: Queue s a -> ST s (Maybe a)
  front q = do
    !isEmpty <- isEmpty q
    if isEmpty then return Nothing else do
      !vec <- readSTRef $ valQueue q
      !st <- readSTRef $ frontPosQueue q
      fmap unwrap <$> Vec.readAt vec st

  enqueue :: Queue s e -> e -> ST s ()
  enqueue q val = do
    (!st, !next) <- getQueuePointers q
    whenM (isFullQueue q) $ do
      !oriLen <- Vec.len =<< readSTRef (valQueue q)
      vec <- readSTRef (valQueue q)
      Vec.enlarge vec (Left ()) $ oriLen * 2  -- automatically enlarge the size by multiplying `2`
      -- !newLen <- Vec.len =<< readSTRef (valQueue q)
      -- copy the first part till `st`
      copyAtVec 0 oriLen st =<< readSTRef (valQueue q)
      writeSTRef (nextPosQueue q) (oriLen + st)
    !len <- Vec.len =<< readSTRef (valQueue q)
    !vec <- readSTRef $ valQueue q
    Vec.writeAt vec next $ Right val
    writeSTRef (nextPosQueue q) $ (next + 1) `mod` len
    where
      copyAtVec src tar len vec =
        case compare len 0 of
          EQ -> return ()
          GT -> do
            ~(Just val) <- Vec.readAt vec src
            Vec.writeAt vec tar val
            copyAtVec (src + 1) (tar + 1) (len - 1) vec
          LT -> error "IMPOSSIBLE."


-- | a queue will automatically enlarge itself
--   and this function is just to test if local capacity is all filled
isFullQueue :: Queue s e -> ST s Bool
isFullQueue q = do
  (!st, !next) <- getQueuePointers q
  !len <- capQueue q
  return $ (next + 1) `mod` len == st

capQueue :: Num b => Queue s e -> ST s b
capQueue q = Vec.len =<< readSTRef (valQueue q)

getQueuePointers :: Queue s e -> ST s (Integer, Integer)
getQueuePointers q = do
  !st <- readSTRef $ frontPosQueue q
  !next <- readSTRef $ nextPosQueue q
  return (st, next)

-- -- >>> testQueue
-- -- (89,Just 11)
-- testQueue = runST $ do
--   (q :: Queue s Int) <- new
--   getQueuePointers q
--   forM_ [0..1000] $ enqueue q
--   -- enqueue q 1
--   -- enqueue q 2
--   -- enqueue q 3
--   -- dequeue q
--   -- dequeue q
--   -- -- dequeue q
--   -- (st, next) <- getQueuePointers q
--   forM_ [0..500] $ const $ dequeue q
--   forM_ [10..99] $ enqueue q
--   forM_ [0..500] $ const $ dequeue q
--   fmap (,) (len q) <*> front q
--   -- getQueuePointers q
--   -- capQueue q
--   -- isEmpty q
--   -- front q
--   -- len <- Vec.len =<< readSTRef (valQueue q)
--   -- return $ (next + 1) `mod` len
--   -- isFullQueue q
