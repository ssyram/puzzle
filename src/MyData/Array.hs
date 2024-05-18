module MyData.Array (
    Array
  , fromList
  , toList
  , (!)
  , (!?)
  , size
  , isEmpty) where

import qualified Data.Array as A
import Test.QuickCheck (Arbitrary)
import Test.QuickCheck.Arbitrary (Arbitrary(arbitrary))
import Control.Monad.Cont (forM)

-- A wrapped, more direct, intuitive and convenient version of `Array`
-- The aim of `Array` is just the speed of accessing

newtype Array e = Arr (A.Array Int e)
  deriving (Eq, Ord, Show)

fromList :: [e] -> Array e
fromList lst = Arr $ A.listArray (0, length lst - 1) lst

toList :: Array e -> [e]
toList (Arr arr) = A.elems arr

(!) :: Array e -> Int -> e
(Arr arr) ! idx = arr A.! idx

(!?) :: Array a -> Int -> Maybe a
(Arr arr) !? idx
  | A.inRange (A.bounds arr) idx = Just $ arr A.! idx
  | otherwise = Nothing

size :: Array e -> Int
size (Arr arr) = snd (A.bounds arr) + 1

isEmpty :: Array e -> Bool
isEmpty (Arr arr) = uncurry (>) $ A.bounds arr

instance Arbitrary e => Arbitrary (Array e) where
  arbitrary = fromList <$> arbitrary
