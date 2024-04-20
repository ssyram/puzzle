{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module StreamProgramming where

newtype Stream m = Stream [m] deriving (Eq, Show, Functor, Applicative, Monad, Semigroup, Monoid)

combine :: (t1 -> t2 -> m) -> Stream t1 -> Stream t2 -> Stream m
combine op (Stream x) (Stream y) =
  case (x, y) of
    ([], _) -> Stream []
    (_, []) -> Stream []
    (x:xs, y:ys) ->
      let (Stream lst) = combine op (Stream xs) (Stream ys) in
      Stream $ op x y : lst

-- >>> filterStream even $ Stream [1,2,3]
-- Stream [2]
filterStream :: (x -> Bool) -> Stream x -> Stream x
filterStream op xs = do
  x <- xs
  if op x then return x else mempty

instance (Num m) => Num (Stream m) where
  (+) = combine (+)
  (*) = combine (*)
  abs = fmap abs
  signum = fmap signum
  fromInteger = return . fromInteger
  negate = fmap negate
instance (Fractional m) => Fractional (Stream m) where
  fromRational = return . fromRational
  (/) = combine (/)
