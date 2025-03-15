{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module LoopQueue where
import qualified Data.Vector.Mutable as VM
import Control.Monad.ST.Strict (ST, stToIO, runST)
import Data.STRef.Strict (STRef)
import Utils (Modifiable(..), eIMPOSSIBLE)
import Control.Monad (when, forM_, foldM)
import Control.Monad.Trans.Writer.Strict (WriterT(runWriterT), execWriterT, tell, execWriter, runWriter)
import Control.Monad.ST.Class (MonadST (..))
import qualified Data.Vector as V
import qualified Data.Sequence as Seq
import qualified Data.Foldable as F
import Debug.Trace (trace)


data Queue s e = Queue
  { values :: STRef s (VM.MVector s e)
  , hdPtr :: STRef s Int
  , nextPtr :: STRef s Int }

new :: MonadST m => m (Queue (World m) e)
new = liftST $ do
  v <- VM.new 2
  v <- newRef v
  hd <- newRef 0
  next <- newRef 0
  return $ Queue v hd next

isEmpty :: MonadST m => Queue (World m) e -> m Bool
isEmpty q = liftST $ do
  hd <- readRef $ hdPtr q
  next <- readRef $ nextPtr q
  return $ hd == next

size :: (MonadST m, Num a) => Queue (World m) e -> m a
size q = liftST $ do
  hd <- readRef $ hdPtr q
  next <- readRef $ nextPtr q
  v <- readRef $ values q
  let len = VM.length v
  return $ fromIntegral $ (next - hd + len) `mod` len

enqueue :: MonadST m => Queue (World m) e -> e -> m ()
enqueue q e = liftST $ do
  v <- readRef $ values q
  hd <- readRef $ hdPtr q
  next <- readRef $ nextPtr q
  let len = VM.length v

  -- Check if it is full
  when (((next + 1) `mod` len) == hd) $ do
      -- trace "enlarge" $ return ()
      newV <- VM.grow v $ max len 1

      -- trace ("next=" ++ show next ++ ";hd="++show hd) $ return ()
      when (next < hd) $ do
        -- trace "move" $ return ()
        -- move elments
        forM_ [0..next-1] $ \i -> do
          e <- VM.read newV i
          VM.write newV (len + i) e
        writeRef (nextPtr q) (len + next)

      writeRef (values q) newV

  v <- readRef $ values q
  let len = VM.length v
  next <- readRef $ nextPtr q
  VM.write v next e
  writeRef (nextPtr q) $ (next + 1) `mod` len
  -- trace "enqueue success" $ return ()

front :: MonadST m => Queue (World m) a -> m (Maybe a)
front q = liftST $ do
  b <- isEmpty q
  if b then return Nothing
  else do
    vd <- readRef $ values q
    hd <- readRef $ hdPtr q
    Just <$> VM.read vd hd

back :: MonadST m => Queue (World m) a -> m (Maybe a)
back q = liftST $ do
  b <- isEmpty q
  if b then return Nothing
  else do
    vd <- readRef $ values q
    let len = VM.length vd
    next <- readRef $ nextPtr q
    let back = if next == 0 then len - 1 else next - 1
    Just <$> VM.read vd back

getAt :: (MonadST m, Integral i) => Queue (World m) e -> i -> m (Maybe e)
getAt q idx = liftST $ do
  size <- size q
  if size <= idx then return Nothing
  else do
    vd <- readRef $ values q
    let len = VM.length vd
    hd <- readRef $ hdPtr q
    let trueIdx = (hd + fromIntegral idx) `mod` len
    Just <$> VM.read vd trueIdx

dequeue :: MonadST m => Queue (World m) a -> m (Maybe a)
dequeue q = liftST $ do
  empty <- isEmpty q
  if empty
    then return Nothing
    else do
      v <- readRef $ values q
      hd <- readRef $ hdPtr q
      e <- VM.read v (fromIntegral hd)
      let newHd = (hd + 1) `mod` VM.length v
      writeRef (hdPtr q) newHd
      return $ Just e

fromList :: MonadST m => [a] -> m (Queue (World m) a)
fromList lst = liftST $ do
  v <- V.unsafeThaw $ V.fromList lst
  let len = VM.length v
  v' <- VM.grow v len
  v <- newRef v'
  hd <- newRef 0
  next <- newRef len
  return $ Queue v hd next

toList :: MonadST m => Queue (World m) a -> m [a]
toList q = liftST $ do
  vd <- readRef $ values q
  let len = VM.length vd
  hd <- readRef $ hdPtr q
  next <- readRef $ nextPtr q
  -- trace ("next=" ++ show next ++ ";hd="++show hd) $ return ()
  if next >= hd then
    V.toList <$> V.freeze (VM.slice hd (next - hd) vd)
  else do  -- next < hd
    pre <- V.toList <$> V.freeze (VM.slice hd (len - hd) vd)
    post <- V.toList <$> V.freeze (VM.slice 0 next vd)
    return $ pre ++ post

testLoopQueueLstOperation :: (Foldable t, Integral a1) => t (a1, a2) -> ([a2], [Maybe a2])
testLoopQueueLstOperation lst = runST $ runWriterT $ do
  q <- new
  forM_ lst $ \(opCode, opItem) ->
    case abs $ opCode `mod` 3 of
      0 -> enqueue q opItem
      1 -> do e <- dequeue q; tell [e]
      2 -> do e <- front q; tell [e]
      _ -> eIMPOSSIBLE
  toList q

seqLstOperation :: (Foldable t, Integral a1) => t (a1, a2) -> ([a2], [Maybe a2])
seqLstOperation lst = runWriter $ do
  q <- foldM folder Seq.empty lst
  return $ F.toList q
  where
    folder q (opCode, opItem) = case abs $ opCode `mod` 3 of
      0 -> return $ q Seq.|> opItem
      1 -> case q of
        Seq.Empty -> do tell [Nothing]; return q
        e Seq.:<| q -> do tell [Just e]; return q
      2 -> case q of
        Seq.Empty -> do tell [Nothing]; return q
        e Seq.:<| _ -> do tell [Just e]; return q
      _ -> eIMPOSSIBLE

testLoopQueue :: [(Int, Int)] -> Bool
testLoopQueue (lst :: [(Int, Int)]) =
  testLoopQueueLstOperation lst == seqLstOperation lst

testGrow :: IO [Int]
testGrow = do
  vec <- VM.generate 3 id
  vec <- VM.grow vec 2
  F.toList <$> V.freeze vec

testInit :: IO [Int]
testInit = do
  vec <- VM.new 8
  VM.write vec 0 0
  VM.write vec 2 0
  VM.write vec 3 0
  VM.copy (VM.slice 0 1 vec) (VM.slice 4 1 vec)
  -- forM_ [2..5] $ \idx -> VM.write vec idx 0
  F.toList <$> V.freeze (VM.slice 2 3 vec)

-- testSome :: IO (Maybe Integer)
-- testSome = do
--   q <- stToIO new
--   stToIO $ enqueue q 1
--   stToIO $ dequeue q
