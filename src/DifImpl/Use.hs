module DifImpl.Use where

import qualified DifImpl.Impl1
import DifImpl.Class (MyClass(someFunc))
-- import qualified DifImpl.Impl2

-- >>> showOne 10
-- 1
showOne :: Int -> Int
showOne = someFunc
