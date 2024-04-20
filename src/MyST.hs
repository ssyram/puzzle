{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module MyST (
  MyST, MySTRef, newMySTRef, readMySTRef, writeMySTRef
) where

-- try using generic to implement a localised ST

import qualified Data.Serialize as Serialize
import qualified Data.HashMap.Strict as Map
import Control.Monad.State.Strict
import Data.ByteString.UTF8
import Control.Monad.ST.Trans
import Utils

newtype MyST s = MyST (State (Int, Map.HashMap Int ByteString) s)
  deriving (Functor, Applicative, Monad)

internalGet :: MyST (Int, Map.HashMap Int ByteString)
internalGet = MyST get
internalPut :: (Int, Map.HashMap Int ByteString) -> MyST ()
internalPut v = MyST $ put v

-- fake `a`, only require the key to search the value
newtype MySTRef a = MySTRef Int

class MySerialise a where
  serialise :: a -> ByteString
  deSerialise :: ByteString -> a

instance Serialize.Serialize a => MySerialise a where
  serialise x = Serialize.runPut $ Serialize.put x
  deSerialise bs =
    case Serialize.runGet Serialize.get bs of
      Left str -> error "Read Error"
      Right str -> str

newMySTRef :: Serialize.Serialize a => a -> MyST (MySTRef a)
newMySTRef a = do
  (nextId, map) <- internalGet
  internalPut (nextId + 1, Map.insert nextId (serialise a) map)
  return $ MySTRef nextId

readMySTRef :: Serialize.Serialize a => MySTRef a -> MyST a
readMySTRef (MySTRef id) = do
  (_, map) <- internalGet
  return $ deSerialise $ map Map.! id

writeMySTRef :: Serialize.Serialize a => MySTRef a -> a -> MyST ()
writeMySTRef (MySTRef id) a = do
  (nextId, map) <- internalGet
  internalPut (nextId, Map.insert id (serialise a) map)
  return ()


-- My MaybeT implementation

data MyMaybeT m t where
  MyMaybeT :: (Monad m) => m (Maybe t) -> MyMaybeT m t

runMyMaybeT :: (Monad m) => MyMaybeT m t -> m (Maybe t)
runMyMaybeT (MyMaybeT x) = x

instance Functor (MyMaybeT m) where
  fmap f (MyMaybeT x) =
    MyMaybeT $ do v <- x
                  case v of
                    Nothing -> return Nothing
                    Just v  -> return $ Just $ f v
instance (Monad m) => Applicative (MyMaybeT m) where
  pure = return
  f <*> x = do
    f <- f
    f <$> x
instance (Monad m) => Monad (MyMaybeT m) where
  return = MyMaybeT . return . return
  (MyMaybeT x) >>= f =
    MyMaybeT $ do x <- x
                  case x of
                    Nothing -> return Nothing
                    Just v  -> runMyMaybeT $ f v
instance MonadTrans MyMaybeT where
  lift = MyMaybeT . (return <$>)

-- My List Monad Transformer

data MyListT m t where
  MyListT :: (Monad m) => { runMyListT :: m [t] } -> MyListT m t
instance Functor (MyListT m) where
  fmap f (MyListT x) = MyListT $ do fmap f <$> x
instance (Monad m) => Applicative (MyListT m) where
  pure = return
  f <*> x = do f <- f; f <$> x
instance (Monad m) => Monad (MyListT m) where
  return = MyListT . return . return
  (MyListT x) >>= f = MyListT $ do lst <- x
                                   fmap (runMyListT . f) lst |> reduceListM $$ return `compose2` (++)
                                   --  applyAndCombine f lst  -- the same as the above 
    where
      applyAndCombine :: Monad m => (a -> MyListT m b) -> [a] -> m [b]
      applyAndCombine f [] = return []
      applyAndCombine f (x:xs) = do
        let (MyListT a) = f x
        preLst <- a
        lst <- applyAndCombine f xs
        return $ preLst ++ lst
instance MonadTrans MyListT where
  lift = MyListT . (return <$>)


{-
  An failing attempt wanting to implement the External version of the monad transformers.
  The difficulty is that when the computation of `f` is completed
  it is hard to re-obtain the internal stuff --
    the information that the result of `f` is `Nothing` exists within the domain of `m`
    but cannot be reflected to the outside world
-}

-- newtype ExternalMaybeT m a = ExternalMaybeT { runExternalMaybeT :: Maybe (m a) }

-- instance (Monad m) => Functor (ExternalMaybeT m) where
--   fmap f (ExternalMaybeT x) = ExternalMaybeT $ fmap f <$> x
-- instance (Monad m) => Applicative (ExternalMaybeT m) where
--   pure = return
--   f <*> x = do { f <- f; f <$> x }
-- instance (Monad m) => Monad (ExternalMaybeT m) where
--   return = ExternalMaybeT . return . return
--   (ExternalMaybeT maybe) >>= f = 
--     case maybe of Nothing -> ExternalMaybeT Nothing
--                   Just md -> ExternalMaybeT $ return $ do
--                     x <- md 
--                     case runExternalMaybeT $ f x of
--                       Nothing -> undefined
--                       Just mb -> undefined
