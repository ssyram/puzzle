{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
module SarHelper () where

import qualified Data.Set as Set
import qualified Data.String as String
import Utils
import Debug.Trace (trace)

-- see the computation time of the collection of values
-- newtype Var = Var Char
-- x :: Var
-- x = Var 'X'
-- y :: Var
-- y = Var 'Y'
-- data Val = Val Integer | Any
-- virtualNodes :: [(Integer,
--   (Integer -> [(Integer, Integer)]) -> [(Integer, Integer)])]
-- virtualNodes :: [(Integer -> [(Integer, Integer)]) -> [(Integer, Integer)]]
virtualNodes =
  [
    const [(0, 0)],
    \pos -> pos 0 ++ pos 6,
    \pos -> filter (\(x, y) -> x <= 100 && y <= 100) $ pos 1,
    \pos -> fstMap (+1) <$> pos 2,
    \pos -> pos 3,
    \pos -> pos 3,
    \pos -> (pos 4 ++) $ sndMap (+1) <$> pos 5,
    \pos -> filter (\(x, y) -> not $ x <= 100 && y <= 100) $ pos 1
  ]
computeVal prev =
  fmap ($ (prev !!)) virtualNodes
iter prev
  | prev == new = new
  | otherwise = iter new
  where
    new = fmap Set.fromList $ computeVal $ fmap Set.toList prev

-- vals :: [Set.Set (Integer, Integer)]
vals :: Int
vals =
  length $ iter $ fmap (const Set.empty) virtualNodes

-- >>> num
num :: Rational
num = 1 - 726838724295606405749951250403292877703036551280076770650817759362733295640543827943771217978833285491456107969707184409286989483921203/726838724295606890549323807888004534353641360687318060281490199180639288113397923326191050713763565560762521606266177933534601628614656

-- Try defining a new number type
newtype MyNum = MyNum Double deriving (Num, Show)

instance Fractional MyNum where
  fromRational :: Rational -> MyNum
  fromRational = MyNum . fromRational
  recip :: MyNum -> MyNum
  recip (MyNum n) = MyNum $ recip n

deriving instance Floating MyNum

data MyNat =
    MyZero
  | MySucc !MyNat
  deriving (Show)

instance Num MyNat where
  (+) :: MyNat -> MyNat -> MyNat
  MyZero     + _      = MyZero
  _          + MyZero = MyZero
  (MySucc x) + y      = MySucc $ x + y
  -- (+) x y = 
  --   case (x, y) of
  --     (MyZero, y)    -> y
  --     (x, MyZero)    -> x
  --     (MySucc x', y) -> MySucc $ x' + y
  (*) :: MyNat -> MyNat -> MyNat
  MyZero * _          = MyZero
  _ * MyZero          = MyZero
  (MySucc MyZero) * y = y
  x * (MySucc MyZero) = x
  (MySucc x') * y     = y + x' * y
  -- (*) x y =
  --   case (x, y) of 
  --     (MyZero, _)        -> MyZero
  --     (_, MyZero)        -> MyZero
  --     (MySucc MyZero, _) -> y
  --     (_, MySucc MyZero) -> x
  --     (MySucc x', _)     -> y + x' * y
  abs :: MyNat -> MyNat
  abs = id
  signum :: MyNat -> MyNat
  signum MyZero     = MyZero
  signum (MySucc _) = MySucc MyZero
    -- \case MyZero -> 0; MySucc _ -> 1
  fromInteger :: Integer -> MyNat
  fromInteger x =
    -- trace "Run `fromInteger`." $  -- to confirm that `1 :: MyNat` is implemented by calling this
    case compare x 0 of
      EQ -> MyZero
      LT -> error "MyNewNum is Positive-Only."
      GT  -> MySucc $ fromInteger $ x - 1
  (-) :: MyNat -> MyNat -> MyNat
  MyZero   - _        = MyZero
  x        - MyZero   = x
  MySucc x - MySucc y = x - y
  -- (-) x y =
  --   case (x, y) of
  --     (MyZero, _) -> MyZero
  --     (_, MyZero) -> x
  --     (MySucc x', MySucc y') -> x' - y'

