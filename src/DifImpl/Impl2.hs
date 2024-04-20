{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
module DifImpl.Impl2 where

import DifImpl.Class

instance Enum t => MyClass t where
  someFunc :: t -> Int
  someFunc = fromEnum
