{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
module TryTaglessFinal where

class (Show v) => Var v where
  mkVar :: String -> v

class (Num c) => Const c

class (Var v, Const c) => Expr e v c where
  eAdd :: (Num n) => e v c n -> e v c n -> e v c n
  eMul :: (Num n) => e v c n -> e v c n -> e v c n
  eMinus :: (Num n) => e v c n -> e v c n -> e v c n
  eCmp :: (Num n) => Ordering -> e v c n -> e v c n -> e v c Bool
  eAnd :: e v c Bool -> e v c Bool -> e v c Bool
  eOr :: e v c Bool -> e v c Bool -> e v c Bool

