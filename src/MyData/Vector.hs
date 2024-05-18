{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
module MyData.Vector (
  Vector,
  new,
  len,
  newWithSize,
  writeAt,
  readAt,
  pushBack,
  enlarge,
  insertAt,
  toList,
  fromList
) where

import Control.Monad.ST
import Data.Array.ST
import Data.STRef
import Control.Monad
import Data.Maybe (maybeToList)
import Utils (Modifiable(readRef))

-- | The ST version of a mutable vector, capable of automatically managing size
data Vector s e = Vector {
  -- | Using `Nothing` as the placeholder for the value
  valVec :: !(STRef s (STArray s Integer (Maybe e))),
  lenVec :: !(STRef s Integer),
  capVec :: !(STRef s Integer)
}

len :: (Num n) => Vector s e -> ST s n
len vec = do
  int <- readSTRef $ lenVec vec
  return $ fromInteger int

new :: ST s (Vector s e)
new = newVector_ 32

newWithSize :: Integral i => e -> i -> ST s (Vector s e)
newWithSize initVal size
  | size < 0 = newWithSize initVal 0
  | otherwise = do
    arr <- newVector_ (fromIntegral size + 32)
    writeSTRef (lenVec arr) $ fromIntegral size
    writeAll arr initVal 0 $ fromIntegral size
    return arr

writeAll :: Integral i => Vector s t -> t -> i -> i -> ST s ()
writeAll vec initVal pos len
  | pos >= len = return ()
  | otherwise  = do
    writeAt vec pos initVal
    writeAll vec initVal (pos + 1) len

newVector_ :: Integer -> ST s (Vector s e)
newVector_ capacity = do
  arr <- newArray (0, capacity - 1) Nothing  -- :: ST s (STArray s Integer (Maybe e))
  valVec <- newSTRef arr
  lenVec <- newSTRef 0 :: ST s (STRef s Integer)
  capVec <- newSTRef capacity :: ST s (STRef s Integer)
  return $ Vector valVec lenVec capVec

-- autoResizeVecCap :: Vector s e -> ST s ()
-- autoResizeVecCap vec =
--   resizeVecCap vec . (+32) =<< readSTRef (capVec vec)

-- | Enlarge the given `vec` by writing the `defaultVal` for the `additionalSize`.
enlarge :: Vector s e -> e -> Integer -> ST s ()
enlarge vec defaultVal additionalSize = do
  oriLen <- readSTRef $ lenVec vec
  oriCap <- readSTRef $ capVec vec
  let newSize = oriLen + additionalSize
  when (newSize > oriCap) $ resizeVecCap vec (newSize + 32)
  writeSTRef (lenVec vec) newSize
  writeAll vec defaultVal oriLen additionalSize

-- -- | resize the whole vector
-- resize :: Vector s e -> e -> Integer -> ST s ()
-- resize vec defaultVal newSize = do
--   oriLen <- readSTRef $ lenVec vec
--   oriCap <- readSTRef $ capVec vec
--   when (newSize > oriCap) $ resizeVecCap vec (newSize + 32)
--   writeSTRef (lenVec vec) newSize
--   when (newSize > oriLen) $ writeAll vec defaultVal

-- -- | automatically enlarge the vector
-- autoResize :: Vector s e -> ST s ()
-- autoResize vec = 
--   resize vec . (+32) =<< readSTRef (lenVec vec)

resizeVecCap :: Vector s e -> Integer -> ST s ()
resizeVecCap vec newCapacity = do
  l <- readSTRef $ lenVec vec
  oriArr <- readSTRef $ valVec vec
  newArr <- newArray (0, newCapacity - 1) Nothing  -- :: ST s (STArray s Integer (Maybe e))
  forM_ [0..min l newCapacity - 1] $ \idx ->
    writeArray newArr idx =<< readArray oriArr idx
  writeSTRef (valVec vec) newArr
  writeSTRef (capVec vec) newCapacity
  writeSTRef (lenVec vec) $ min l newCapacity

pushBack :: Vector s e -> e -> ST s ()
pushBack vec v = do
  l <- readSTRef $ lenVec vec
  c <- readSTRef $ capVec vec
  when (l + 1 >= c) $ resizeVecCap vec (c + 32)
  arr <- readSTRef $ valVec vec
  writeArray arr l $ Just v
  writeSTRef (lenVec vec) $ l + 1

readAt :: Integral i => Vector s a -> i -> ST s (Maybe a)
readAt vec idx = do
  !lenv <- readSTRef $ lenVec vec
  if lenv <= fromIntegral idx || idx < 0 then return Nothing
  else do
    arr <- readSTRef (valVec vec)
    ele <- readArray arr $ fromIntegral idx
    case ele of
      Nothing -> error $ "Read Undefined Value, at position " ++ show (fromIntegral idx) ++ "."
      Just e  -> return $ Just e

-- | returns whether write succeeded
--   may fail to write iff it is out of the bound of length
writeAt :: Integral i => Vector s e -> i -> e -> ST s Bool
writeAt vec idx val = do
  idx <- return $ fromIntegral idx
  !lenv <- readSTRef $ lenVec vec
  if lenv <= idx || idx < 0 then return False
  else do
    arr <- readSTRef (valVec vec)
    writeArray arr idx (Just val)
    return True

-- | May insert at the back to create a new position
insertAt :: Vector s e -> Integer -> e -> ST s Bool
insertAt vec idx val = do
  !lenv <- readSTRef $ lenVec vec
  if lenv < idx || idx < 0 then return False
  else do
    c <- readSTRef (capVec vec)
    when (lenv + 1 >= c) $ resizeVecCap vec (c + 32)
    !arr <- readSTRef $ valVec vec
    forM_ [lenv, lenv - 1..idx + 1] $ \idx -> do
      writeArray arr (idx - 1) =<< readArray arr idx
    writeArray arr idx $ Just val
    modifySTRef (lenVec vec) (+1)
    return True

fromList :: [a] -> ST s (Vector s a)
fromList lst = do
  let len = length lst
  v <- newVector_ $ fromIntegral len
  forM_ lst $ pushBack v
  return v

collect :: (t -> Maybe b) -> [t] -> [b]
collect f lst = do
  x <- lst
  maybeToList $ f x

toList :: Vector s b -> ST s [b]
toList v = do
  v <- readRef $ valVec v
  collect id <$> getElems v
