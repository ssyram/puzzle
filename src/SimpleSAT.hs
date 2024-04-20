{-# LANGUAGE Strict #-}
module SimpleSAT where

import Utils
import Data.Either
import Test.QuickCheck

data Literal a = Pos a | Neg a

newtype Clause a = Clause [Either Bool (Literal a)]

simplifyClause :: Clause a -> Either Bool (Clause a)
simplifyClause (Clause lst) =
  let l = [x | e <- lst, isLeft e, let ~(Left x) = e] in
  if null l then Right $ Clause lst else Left $ and l

data RoseTree a = RoseTree a [RoseTree a]

