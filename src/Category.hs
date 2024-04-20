{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
module Category where

-- This file is for Category theory learning

{- | Pairing for object A and object B is a triple (P, proj1, proj2)

where P is an object and proj1 and proj2 are two morphisms to ``extract information from P''.
-}
class Pairing a b p where
  projA :: p -> a
  projB :: p -> b

instance Pairing a b (a, b) where
  projA :: (a, b) -> a
  projA (a, b) = a
  projB :: (a, b) -> b
  projB (a, b) = b


