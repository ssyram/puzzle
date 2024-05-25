module TryLogict where

import Control.Monad.Logic
import Control.Applicative
import Control.Monad.Trans.Reader

type LockCode = (Char, Char, Char)

codes :: [LockCode]
codes = do
  a <- ['A'..'Z']
  b <- ['A'..'Z']
  c <- ['A'..'Z']
  return (a,b,c)

-- | Convert any foldable, including list to alternative structures
choose :: (Foldable t, Alternative f) => t a -> f a
choose = foldr ((<|>) . pure) empty

fromList lst = msum $ fmap return lst

-- | A List implementation of the validCodes -- which should give us directly the result
--   In this case, using `Logic` and `List` are mostly the same -- the better performance
--   provided by the `Logic` Monad seems not used here.
-- >>> listValidCodes
-- [('K','F','C')]
listValidCodes :: [LockCode]
listValidCodes = do
  code@(a, b, c) <- codes  -- changes Nothing whether `choose` is applied
  -- ABC: One digit is correct and well placed
  guard $ (a == 'A' && b /= 'B' && c /= 'C') ||
          (a /= 'A' && b == 'B' && c /= 'C') ||
          (a /= 'A' && b /= 'B' && c == 'C')
  -- AEF: One digit is correct and wrongly placed
  guard $ (a /= 'A' && (b == 'A' || c == 'A')) ||
          (b /= 'E' && (a == 'E' || c == 'E')) ||
          (c /= 'F' && (a == 'F' || b == 'F'))
  -- CKA: Two digits are correct but wrongly placed
  guard $ (length (filter (`elem` "CKA") [a, b, c]) == 2) &&
          not (a == 'C' || b == 'K' || c == 'A')
  -- DEB: No digits are correct
  guard $ all (`notElem` "DEB") [a, b, c]
  -- BDK: One digit is correct but wrongly placed
  guard $ (b /= 'B' && (a == 'B' || c == 'B')) ||
          (b /= 'D' && a /= 'D' && c == 'D') ||
          (b /= 'K' && a == 'K' && c /= 'K')
  return code

validCodes :: Logic LockCode
validCodes = do
  code@(a, b, c) <- choose codes
  -- ABC: One digit is correct and well placed
  guard $ (a == 'A' && b /= 'B' && c /= 'C') ||
          (a /= 'A' && b == 'B' && c /= 'C') ||
          (a /= 'A' && b /= 'B' && c == 'C')
  -- AEF: One digit is correct and wrongly placed
  guard $ (a /= 'A' && (b == 'A' || c == 'A')) ||
          (b /= 'E' && (a == 'E' || c == 'E')) ||
          (c /= 'F' && (a == 'F' || b == 'F'))
  -- CKA: Two digits are correct but wrongly placed
  guard $ (length (filter (`elem` "CKA") [a, b, c]) == 2) &&
          not (a == 'C' || b == 'K' || c == 'A')
  -- DEB: No digits are correct
  guard $ all (`notElem` "DEB") [a, b, c]
  -- BDK: One digit is correct but wrongly placed
  guard $ (b /= 'B' && (a == 'B' || c == 'B')) ||
          (b /= 'D' && a /= 'D' && c == 'D') ||
          (b /= 'K' && a == 'K' && c /= 'K')
  return code

-- >>> realCodes
-- [('K','F','C')]
realCodes :: [LockCode]
realCodes = observeAll validCodes

-- >>> tryOrder :: [(Char, Char, Char)]
-- [('A','A','A'),('A','A','B'),('A','A','C'),('A','B','A'),('A','B','B'),('A','B','C'),('A','C','A'),('A','C','B'),('A','C','C'),('B','A','A'),('B','A','B'),('B','A','C'),('B','B','A'),('B','B','B'),('B','B','C'),('B','C','A'),('B','C','B'),('B','C','C'),('C','A','A'),('C','A','B'),('C','A','C'),('C','B','A'),('C','B','B'),('C','B','C'),('C','C','A'),('C','C','B'),('C','C','C')]
-- >>> observeAll tryOrder
-- [('A','A','A'),('A','A','B'),('A','A','C'),('A','B','A'),('A','B','B'),('A','B','C'),('A','C','A'),('A','C','B'),('A','C','C'),('B','A','A'),('B','A','B'),('B','A','C'),('B','B','A'),('B','B','B'),('B','B','C'),('B','C','A'),('B','C','B'),('B','C','C'),('C','A','A'),('C','A','B'),('C','A','C'),('C','B','A'),('C','B','B'),('C','B','C'),('C','C','A'),('C','C','B'),('C','C','C')]
tryOrder :: (Monad m, Alternative m) => m (Char, Char, Char)
tryOrder = do
  a <- choose ['A'..'C']
  b <- choose ['A'..'C']
  c <- choose ['A'..'C']
  return (a, b, c)

-- >>> seeIfTheSame
-- True
seeIfTheSame :: Bool
seeIfTheSame =
  tryOrder == observeAll tryOrder

tryFairness :: Logic Int
tryFairness = choose [1..] `interleave` choose [0]

tryForLogic :: Logic Int
tryForLogic = do
  val <- tryFairness
  guard $ val <= 0
  return val


type LogicWithDataBase d t = LogicT (Reader d) t

readData :: LogicWithDataBase d d
readData = lift ask
