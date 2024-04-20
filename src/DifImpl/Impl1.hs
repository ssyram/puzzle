{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
module DifImpl.Impl1 where

import DifImpl.Class

instance MyClass t where
  someFunc :: t -> Int
  someFunc = const 1
