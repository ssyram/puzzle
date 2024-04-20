{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wunused-binds #-}
{-# OPTIONS_GHC -Wno-typed-holes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" #-}
module MyMonads where
import Control.Monad.Cont (liftM, MonadTrans, lift, MonadIO (liftIO))
import Control.Monad
import Control.Monad.Identity (Identity (runIdentity, Identity))
import Control.Applicative (Alternative)
import Control.Monad.ST.Trans (STT)
import Data.IORef (newIORef, writeIORef, readIORef)
import Utils

-- Types with final character `D` means 'Directly' rather than from its Monad Transformer

-- ================================= My Cont and ContT =================================

{-| A ```Cont r a``` represents a computation aiming at final value of type `r` and 
-}
newtype ContD r a = ContD { runContD :: (a -> r) -> r }

instance Monad (ContD r) where
  return :: a -> ContD r a
  return a = ContD ($ a)
  (>>=) :: ContD r a -> (a -> ContD r b) -> ContD r b
  (ContD cf) >>= f = ContD $ \cont ->
    cf $ \a ->
      let some = runContD $ f a in
      some cont

instance Functor (ContD r) where
  fmap :: (a -> b) -> ContD r a -> ContD r b
  fmap = liftM
instance Applicative (ContD r) where
  pure :: a -> ContD r a
  pure = return
  (<*>) :: ContD r (a -> b) -> ContD r a -> ContD r b
  (<*>) = ap

newtype ContT r m a = ContT { runContT :: (a -> m r) -> m r }

instance Monad m => Monad (ContT r m) where
  return :: Monad m => a -> ContT r m a
  return a = ContT ($ a)
  -- The simplified implementation converted from the next function
  (>>=) :: Monad m => ContT r m a -> (a -> ContT r m b) -> ContT r m b
  (ContT cont) >>= f = ContT $ \func ->
    cont $ flip runContT func . f
  -- The usual implementation, a version before simplification
  -- (ContT cf) >>= f = ContT $ \bf ->
  --   cf $ \a -> 
  --     runContT (f a) bf

instance Monad m => Functor (ContT r m) where
  fmap :: Monad m => (a -> b) -> ContT r m a -> ContT r m b
  fmap f (ContT cf) = ContT $ \bf ->
    cf $ \a -> bf $ f a
instance Monad m => Applicative (ContT r m) where
  pure :: Monad m => a -> ContT r m a
  pure = return
  (<*>) :: Monad m => ContT r m (a -> b) -> ContT r m a -> ContT r m b
  (<*>) = ap

instance MonadTrans (ContT r) where
  lift :: Monad m => m a -> ContT r m a
  lift = ContT . (>>=)

type Cont r a = ContT r Identity a

runCont :: Cont r a -> (a -> r) -> r
runCont t cont = runIdentity $ runContT t $ \a -> return $ cont a

cont :: ((a -> r) -> r) -> Cont r a
cont f = ContT $ \cont ->
  Identity $ f $ \a -> runIdentity $ cont a

evalContT :: Monad m => ContT r m r -> m r
evalContT = flip runContT return

-- | This function delimits the computation
resetT :: Monad m => ContT r m r -> ContT r' m r
resetT = lift . evalContT

-- | This function delimits the computation
reset :: Cont r r -> Cont r' r
reset = resetT

evalCont :: Cont r r -> r
evalCont = runIdentity . evalContT

-- | This function captures the whole rest of the computation (till the nearest outside reset)
--   and put the captured computation into input `f`
shiftT :: Monad m => ((a -> m r) -> ContT r m r) -> ContT r m a
shiftT f = ContT $ evalContT . f

-- | This function captures the whole rest of the computation (till the nearest outside reset)
--   and put the captured computation into input `f`
shift :: ((a -> r) -> Cont r r) -> Cont r a
shift f = shiftT $ f . (runIdentity .)

callCC :: ((forall b. a -> ContT r m b) -> ContT r m a) -> ContT r m a
callCC f = ContT $ \cf ->
  runContT (f $ \a -> ContT $ \_ -> cf a) cf

-- | Now, the bounded `return` function is a TRUE `return` function in the sense of C language
--   Usually use the name `exit` to distinguish
-- >>> evalCont exampleCallCC
-- 11
exampleCallCC :: (Monad m, Num a, Enum a, Ord a) => ContT r m a
exampleCallCC = callCC $ \return -> do
  forM_ [1..] $ \i -> do
    when (i > 10) $ return $ error "Exception Mark."  -- will return this value
    doSomething i  -- do anything someone would like to work with `i`
  return (-1)  -- the final return statement, yet will never be called
  where
    doSomething _ = return ()

-- | The `break` function in the sense of C language
cBreak :: Monad m => ContT () m a
cBreak = shiftT $ const $ return ()

instance (Monad m, MonadIO m) => MonadIO (ContT r m) where
  liftIO :: (Monad m, MonadIO m) => IO a -> ContT r m a
  liftIO io = lift $ liftIO io

-- | The example of trying to use `break`
--   Also, the `MonadIO` is used here to try to perform things like the C language
--   The control flow can be taken care of by `Cont` and one can do the actual stuff via lifting
exampleUseBreak :: (MonadIO m, Num b, Enum b, Ord b, Show b) => ContT r' m b
exampleUseBreak = do
  val <- liftIO $ newIORef 1
  resetT $ forM_ [1..] $ \i -> do
    when (i > 10) cBreak
    doSomething val i
  i <- liftIO $ readIORef val
  liftIO $ print i
  return i
  where
    doSomething val i = do
      curVal <- liftIO $ readIORef val
      liftIO $ putStrLn $ "Current val: " ++ show curVal
      liftIO $ putStrLn $ "val <<- " ++ show i
      liftIO (val <<- i)

runExampleUseBreak :: (Num r, Enum r, Ord r, Show r) => IO r
runExampleUseBreak = evalContT exampleUseBreak

-- | A dropping example that after shift, only the content within it will be utilised.
--   The later content is dropped / captured into the shift context
-- >>> exampleDrop
-- "Only here works. And here!"
exampleDrop :: String
exampleDrop = evalCont $ do
  hint <- reset $ do
    -- by using shift, the content from outside is totally discarded
    x <- shift $ \_ -> return "Only here works"
    -- this `y` is also not going to be used
    let _y = x + 1
    return "Some non-working stuff"
  return $ hint ++ ". And here!"

-- =================================== A Simple Collection Type ===================================

-- | to collect the information from a program, once collected, ignore the later computation
newtype Collection tar tmp =
  Collection { toEither :: Either tar tmp }
  deriving (Eq, Show, Functor, Applicative, Monad, Alternative)

-- | get from the return result -- must finish computation -- if not collected, use the final result
getCollectResult :: Collection a a -> a
getCollectResult (Collection col) =
  case col of
    Left l -> l
    Right l -> l

execCollection :: Collection a a -> a
execCollection = getCollectResult

-- | collect the result here and end the rest of the computation
collect :: a -> Collection a b
collect a = Collection $ Left a

-- | The `fromList` is from left
-- The implementation below has been PROVED by Coq
-- It is a true Monad Transformer
data LogicT m a where
  LogicT :: (Monad m) =>
    { runLogicT :: forall r . (a -> m r -> m r) -> m r -> m r }
    -> LogicT m a

instance Monad m => Functor (LogicT m) where
  fmap :: Monad m => (a -> b) -> LogicT m a -> LogicT m b
  fmap f (LogicT lf) = LogicT $ \foldFunc -> lf (foldFunc . f)

instance Monad m => Applicative (LogicT m) where
  pure :: Monad m => a -> LogicT m a
  pure = return
  (<*>) :: Monad m => LogicT m (a -> b) -> LogicT m a -> LogicT m b
  (<*>) = ap

instance Monad m => Monad (LogicT m) where
  return :: Monad m => a -> LogicT m a
  return a = LogicT $ \f -> f a
  (>>=) :: Monad m => LogicT m a -> (a -> LogicT m b) -> LogicT m b
  (LogicT lf) >>= f = LogicT $ \foldFunc -> lf $ \a -> runLogicT (f a) foldFunc

instance MonadTrans LogicT where
  lift :: Monad m => m a -> LogicT m a
  lift ma = LogicT $ \f mr -> do { a <- ma; f a mr }

type Logic = LogicT Identity

runLogic :: Logic a -> (a -> r -> r) -> r -> r
runLogic (LogicT lf) f init =
  runIdentity $ lf (\a id -> Identity $ f a (runIdentity id)) $ Identity init

fromList :: (Monad m) => [a] -> LogicT m a
fromList [] = LogicT (\ _f mr -> mr)
fromList (a : as) = LogicT $ \foldFunc init ->
  runLogicT (fromList as) foldFunc $ foldFunc a init

data FoldableThing a where
  FoldableThing :: (Foldable f) => f a -> FoldableThing a

-- | The same type as `FoldableThing` without using GADT
--   the `ExistentialQuantification` is applied to the constructor
--   the `forall` is given BEFORE the constructor
--   if WITHIN the constructor, the `f` to give MUST ACCEPT ANYTHING
data NewFoldable a =
    forall f. (Foldable f) => NewFoldable !(f a)
  | forall t. (Traversable t) => NewFoldable' !(t a)

newFoldableToFoldableThing :: NewFoldable a -> FoldableThing a
newFoldableToFoldableThing (NewFoldable f) = FoldableThing f
newFoldableToFoldableThing (NewFoldable' _t) = FoldableThing []

class ListLike t where
  ofList :: [a] -> t a
  toList :: t a -> [a]

instance ListLike FoldableThing where
  ofList :: [a] -> FoldableThing a
  ofList as = FoldableThing as
  toList :: FoldableThing a -> [a]
  toList (FoldableThing f) = foldr (:) [] f

instance ListLike Logic where
  ofList :: [a] -> Logic a
  ofList [] = LogicT (\ _f mr -> mr)
  ofList (a : as) = LogicT $ \foldFunc init ->
    runLogicT (ofList as) foldFunc $ foldFunc a init
  toList :: Logic a -> [a]
  toList l = runLogic l (:) []

newtype MyContT m a = MyContT (m a)

instance Monad m => Functor (MyContT m) where
  fmap :: Monad m => (a -> b) -> MyContT m a -> MyContT m b
  fmap fab (MyContT ma) = MyContT (fmap fab ma)
  -- fmap f (MyContT ma) = MyContT $ f <$> ma

instance Monad m => Applicative (MyContT m) where
  pure :: Monad m => a -> MyContT m a
  pure = return
  (<*>) :: Monad m => MyContT m (a -> b) -> MyContT m a -> MyContT m b
  (<*>) f a = do { f <- f; f <$> a; }

instance Monad m => Monad (MyContT m) where
  return :: Monad m => a -> MyContT m a
  return a = MyContT $ return a
  (>>=) :: Monad m => MyContT m a -> (a -> MyContT m b) -> MyContT m b
  (>>=) (MyContT ma) f = MyContT $ do
    a <- ma
    let (MyContT mb) = f a
    mb

instance MonadTrans MyContT where
  lift :: Monad m => m a -> MyContT m a
  lift ma = MyContT ma

testShow :: String
testShow = runCont (return 10 :: forall r. Cont r Int) show

-- >>> take 10 $ drop 1000 primes
-- [7927,7933,7937,7949,7951,7963,7993,8009,8011,8017]
primes :: [Integer]
primes = filterPrime [2..] where
  filterPrime ~(p:xs) =
    p : filterPrime [x | x <- xs, x `mod` p /= 0]

-- >>> take 10 posNat
-- [1,2,3,4,5,6,7,8,9,10]
posNat :: [Double]
posNat = 1 : fmap (+1) posNat

-- | This function is for re-call to recompute the `primes` so to confirm
--   that the `primes` is call-by-need -- the value is stored.
reTake :: Int -> [Integer]
reTake n = take 10 $ drop n primes
