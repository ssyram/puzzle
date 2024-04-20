{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module MonadTransformer where
import Control.Monad
import Data.Foldable
import Utils
import Control.Monad.Trans.Class
import Control.Applicative (Applicative(..))
import Control.Monad.State
import Control.Monad.Identity (Identity (runIdentity))
import Data.Map (Map)
import Data.Set (Set)

-- Try monad transformer

data MyListT m e where
  MyListT :: (Monad m) => { runMyListT :: m [e] } -> MyListT m e

instance Functor (MyListT m) where
  fmap :: (a -> b) -> MyListT m a -> MyListT m b
  fmap f (MyListT m) = MyListT $ fmap f <$> m

instance (Monad m) => Applicative (MyListT m) where
  pure :: a -> MyListT m a
  pure = return
  (<*>) :: MyListT m (a -> b) -> MyListT m a -> MyListT m b
  f <*> m = do
    f <- f
    fmap f m

instance (Monad m) => Monad (MyListT m) where
  return :: a -> MyListT m a
  return e = MyListT $ return [e]
  (>>=) :: MyListT m a -> (a -> MyListT m b) -> MyListT m b
  (MyListT m) >>= f = MyListT $ do
    lst <- m
    concatM $ fmap (tMap f) lst
    where
      tMap :: (t -> MyListT m e) -> t -> m [e]
      tMap f e = let (MyListT m) = f e in m
      concatM :: (Traversable t, Monad m, Monoid (t x)) => t (m (t x)) -> m (t x)
      concatM (lst :: t (m (t x))) =
        fold <$> sequence lst

instance MonadTrans MyListT where
  lift :: Monad m => m a -> MyListT m a
  lift m = MyListT $ fmap return m

chainM :: (Monad m) => [m x] -> m [x]
chainM = foldr
  (\x lst -> do
    x   <- x
    lst <- lst
    return $ x : lst)
  (return [])

-- | Another, more direct implementation
(>>>=) :: MyListT m e1 -> (e1 -> MyListT m e2) -> MyListT m e2
(MyListT m) >>>= f = MyListT $ do
  lst <- m
  appAndCombine f lst
  where
    appAndCombine f [] = return []
    appAndCombine f (x : lst) = do
      let (MyListT m) = f x
      internalLst <- m
      latterLst <- appAndCombine f lst
      return $ internalLst ++ latterLst

testV :: Int -> MyListT [] Int
testV 0 = MyListT [[0, 1]]
testV 1 = MyListT [[0], [1]]
testV k = return k  -- unused dummy one

-- `MyListT m` may NOT always be a valid Monad -- it is not necessarily associative
-- It is a valid Monad iff the given Monad `m` is COMMUNITATIVE
-- >>> testFunc1
-- [[0,1,0,0,1],[0,1,1,0,1],[0,1,0,0],[0,1,0,1],[0,1,1,0],[0,1,1,1]]
testFunc1 :: [[Int]]
testFunc1 = runMyListT $ (testV >=> testV) >=> testV $ 0
-- >>> testFunc2
-- [[0,1,0,0,1],[0,1,0,0],[0,1,0,1],[0,1,1,0,1],[0,1,1,0],[0,1,1,1]]
testFunc2 :: [[Int]]
testFunc2 = runMyListT $ testV >=> (testV >=> testV) $ 0
-- >>> testFuncSupport 0
-- [[0,1,0],[0,1,1]]
-- >>> testFuncSupport 1
-- [[0,1],[0],[1]]
testFuncSupport :: Int -> [[Int]]
testFuncSupport n = runMyListT $ testV >=> testV $ n

data MyStateT s m a where
  MyStateT :: (Monad m) => { runMyStateT :: s -> m (a, s) } -> MyStateT s m a

instance Functor (MyStateT s m) where
  fmap :: (a -> b) -> MyStateT s m a -> MyStateT s m b
  fmap f (MyStateT st) = MyStateT $ \s -> do
    ~(a, s) <- st s
    return (f a, s)

instance (Monad m) => Applicative (MyStateT s m) where
  pure :: Monad m => a -> MyStateT s m a
  pure = return
  liftA2 :: Monad m =>
    (a -> b -> c) -> MyStateT s m a -> MyStateT s m b -> MyStateT s m c
  liftA2 f sta stb = do
    a <- sta
    f a <$> stb

-- | use liftA2 <*> to use as this
applicative :: (Applicative f) => f (a -> b) -> f a -> f b
applicative = liftA2 ($)

-- | use <*> to implement liftA2
liftA2' :: Applicative f => (a1 -> a2 -> b) -> f a1 -> f a2 -> f b
liftA2' f a b = f <$> a <*> b

liftA3' :: Applicative f => (a1 -> b1 -> a2 -> b2) -> f a1 -> f b1 -> f a2 -> f b2
liftA3' f a b c =
  liftA2 f a b <*> c

instance (Monad m) => Monad (MyStateT s m) where
  return :: Monad m => a -> MyStateT s m a
  return a = MyStateT $ \s -> return (a, s)
  (>>=) :: Monad m => MyStateT s m a -> (a -> MyStateT s m b) -> MyStateT s m b
  (MyStateT st) >>= f = MyStateT $ \s -> do
    ~(a, s) <- st s
    runMyStateT (f a) s

instance MonadTrans (MyStateT s) where
  lift :: Monad m => m a -> MyStateT s m a
  lift m = MyStateT $ \s -> fmap (,s) m

-- (>=>) :: Monad m => (a -> m b) -> (b -> m c) -> a -> m c
-- ma >=> mb = \a -> ma a >>= mb


-- =========================== An Unavailing Try of StateT ===========================

-- | This is IMPOSSIBLE -- the Monad is not implementable -- 
-- the value change is not possible because it is not possible to extract the value
-- from Monad without guarded
data MyNewStateT m s a where
  MyNewStateT :: Monad m => { runMyNewStateT :: m (s -> (a, s)) } -> MyNewStateT m s a

instance Functor (MyNewStateT m s) where
  fmap :: (a -> b) -> MyNewStateT m s a -> MyNewStateT m s b
  fmap f (MyNewStateT st) = MyNewStateT $ do
    st <- st
    return $ \s -> fstMap f $ st s

instance (Monad m) => Applicative (MyNewStateT m s) where
  pure :: Monad m => a -> MyNewStateT m s a
  pure = return
  (<*>) :: Monad m => MyNewStateT m s (a -> b) -> MyNewStateT m s a -> MyNewStateT m s b
  f <*> st = do f <- f; fmap f st

instance (Monad m) => Monad (MyNewStateT m s) where
  return :: a -> MyNewStateT m s a
  return a = MyNewStateT $ return (a,)
  (>>=) :: Monad m => MyNewStateT m s a -> (a -> MyNewStateT m s b) -> MyNewStateT m s b
  (MyNewStateT m) >>= f = MyNewStateT $ do
    st <- m
    -- This is IMPOSSIBLE -- the value cannot be extracted without guarded
    return $ \s -> do
      let (a, s') = st s
      let ~(MyNewStateT m) = f a
      undefined

-- ===================================== End Try =====================================

data MyMaybeT m t where
  MyMaybeT :: Monad m => { runMyMaybeT :: m (Maybe t) } -> MyMaybeT m t

instance (Monad m) => Functor (MyMaybeT m) where
  fmap :: (a -> b) -> MyMaybeT m a -> MyMaybeT m b
  fmap f m = MyMaybeT $ fmap f <$> runMyMaybeT m

instance (Monad m) => Applicative (MyMaybeT m) where
  pure :: Monad m => a -> MyMaybeT m a
  pure = return
  (<*>) :: Monad m => MyMaybeT m (a -> b) -> MyMaybeT m a -> MyMaybeT m b
  (<*>) = ap

instance (Monad m) => Monad (MyMaybeT m) where
  return :: Monad m => a -> MyMaybeT m a
  return = MyMaybeT . return . return
  (>>=) :: Monad m => MyMaybeT m a -> (a -> MyMaybeT m b) -> MyMaybeT m b
  (MyMaybeT m) >>= f = MyMaybeT $ do
    maybe <- m
    case maybe of
      Nothing -> return Nothing
      Just a -> runMyMaybeT $ f a
  
instance MonadTrans MyMaybeT where
  lift :: Monad m => m a -> MyMaybeT m a
  lift = MyMaybeT . fmap Just

instance (Monad m) => MonadState s (MyStateT s m) where
  state :: Monad m => (s -> (a, s)) -> MyStateT s m a
  state st = MyStateT $ return . st

-- ==================================== Try using the transformers ====================================

maybeStateExample :: (Num p) => MyMaybeT (MyStateT p Identity) p
maybeStateExample = do
  some <- action1
  lift $ put $ translate some
  val <- lift get
  return $ val + 1
  where
    action1 = MyMaybeT $ return Nothing
    translate :: Num p => Char -> p
    translate 'c' = 1
    translate _   = undefined

-- >>> runMaybeStateExample
-- (Nothing,0)
runMaybeStateExample :: (Maybe Integer, Integer)
runMaybeStateExample =
  runIdentity $ runMyStateT (runMyMaybeT maybeStateExample) 0
