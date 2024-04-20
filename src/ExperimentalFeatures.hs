{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module ExperimentalFeatures where
import GHC.TypeNats
import Data.Set
import Data.IORef
data T a where
  T1 :: Bool -> T Bool
  T2 :: T a

-- Type inference could happen for different branches
-- >>> f (T1 True) True
f :: T a -> a -> a
f x y = case x of T1 x -> True
                  T2   -> y

data LenVec n a where
  LVNil :: LenVec 0 a
  LVCons :: a -> LenVec n a -> LenVec (n + 1) a

exactlyOne :: LenVec 2 a -> a
exactlyOne lst = case lst of { LVCons a (LVCons b lv) -> a }

-- data Nat = N | S Nat

bind :: (Monad m) => m a -> (a -> m b) -> m b
bind x f = join $ fmap f x

ffmap :: (Monad m) => (a -> b) -> m a -> m b
ffmap f x = x >>= return . f

join :: Monad m => m (m b) -> m b
join x = x >>= id 

data Optional a = Some a | None deriving (Functor)

instance Applicative Optional where
  pure = return
  fo <*> x = do f <- fo
                f <$> x

instance Monad Optional where
  return x = Some x
  x >>= f  = case x of { Some x -> f x; None -> None }

left n (l, r) =
  if abs (l + n - r) > 3 then None
  else return (l + n, r)
right n (l, r) =
  if abs (r + n - l) > 3 then None
  else return (l, r + n)

data List a = Cons a (List a) | Nil deriving (Functor)

instance Applicative List where
  pure = return
  fl <*> xl = do f <- fl
                 f <$> xl

instance Monad List where
  return x = Cons x Nil
  lst >>= f = flat (fmap f lst)

flat :: List (List a) -> List a
flat (Cons l lst) = concate l (flat lst)
flat Nil = Nil
concate :: List a -> List a -> List a
concate Nil lst = lst
concate (Cons a l) lst = Cons a (concate l lst)

cartesianProduct l1 l2 = do e1 <- l1
                            e2 <- l2
                            return (e1, e2)

newtype MyState s a = MyState { myRunState :: s -> (a, s) }

-- instance (Monad m) => Functor m where
--   fmap f = (>>= return . f)

instance Functor (MyState s) where
  fmap f = (>>= return . f)

instance Applicative (MyState s) where
  pure = return
  -- f_st <*> st = MyState $ \s ->
  --   let (f, ns) = myRunState f_st s in
  --   let (a, nns) = myRunState st ns in
  --   (f a, nns)
  f_st <*> st = do f <- f_st
                   f <$> st

instance Monad (MyState s) where
  return x = MyState (x,)
  st >>= f  = MyState (\s ->
                let (a, ns) = myRunState st s in
                myRunState (f a) ns
              )

execMyState st v = fst (myRunState st v)
get () = MyState (\s -> (s, s))
put v = MyState (const ((), v))

myState = plus1 () >> plus1 () >> get ()
  where
    plus1 () = do { n <- get (); put (n + 1); }

-- >>> testMyState
-- 3
testMyState = execMyState myState 1

test3 = (1,,2,,4)

type family Foo x (y :: Nat) :: * -> *

type instance Foo Int 0 = []

data family Nata x :: * -> *

data instance Nata Int Char

data family NMap f

-- data instance NMap Int = NMapInt

-- data instance NMap Bool = NMapBool

data instance NMap a where
  NMapA :: (Enum a) => a -> NMap a

func :: (Ord f) => NMap f -> NMap Int
func (NMapA n) = NMapA (fromEnum n)

-- the second is for distinguish whether it is a default implementation or other kinds
type family NSet e (b :: Bool)

type instance NSet Bool True  = (Bool, Bool)
type instance NSet d False = Set d

data family DSet e (b :: Bool)

newtype instance DSet e False = DSetDefault (Set e)

data FoldableThing a where
  FoldableThing :: Foldable t => t a -> FoldableThing a
  -- the same, but add a "forall" quantifier
  SameFoldableThing :: forall t a. Foldable t => t a -> FoldableThing a
-- the same meaning with two different ways of writing
data FoldableThing' a = forall t.Foldable t => FoldableThing' (t a)

data FoldableThing'' a where
  FoldableThing'' :: Foldable t => t a -> FoldableThing'' (t a)

class RetFoldable'' t where retOne :: t -> FoldableThing'' t

instance RetFoldable'' [Int] where
  retOne lst = FoldableThing'' lst

data FoldableContent lst where
  FoldableContent :: Foldable t => t a -> FoldableContent (t a)
