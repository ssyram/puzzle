{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
module MyData.SimpleQueue where

import Control.Monad.ST
import Data.Array.ST
import Data.STRef
import Data.Maybe
import MyData.QueueClass

newtype Queue s e = Queue {
  valQueue :: STRef s [e]
}

instance STQueue Queue where
  new :: ST s (Queue s e)
  new = Queue <$> newSTRef []
  front :: Queue s e -> ST s (Maybe e)
  front q = listToMaybe <$> readSTRef (valQueue q)
  enqueue :: Queue s e -> e -> ST s ()
  enqueue q val = modifySTRef (valQueue q) (++ [val])
  dequeue :: Queue s e -> ST s (Maybe e)
  dequeue q = 
    readSTRef (valQueue q) >>= \case
      []   -> return Nothing
      x:tl -> do
        writeSTRef (valQueue q) tl
        return $ return x
  len :: Num n => Queue s e -> ST s n
  len q = fromIntegral . length <$> readSTRef (valQueue q)
  isEmpty :: Queue s e -> ST s Bool
  isEmpty q = null <$> readSTRef (valQueue q)
