{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Utils where

import Control.Monad.State.Strict
import Data.List
import Test.QuickCheck
import Control.Monad.ST
import Data.Array.ST
import Data.STRef
import Data.IORef
import qualified Data.HashTable.ST.Basic as HashMap
import qualified Control.Monad.ST.Trans as STT
import Data.Hashable
import Data.Foldable
import Control.Monad.Except (runExceptT)
import Documentation.SBV.Examples.ProofTools.BMC (S(x))
import Debug.Trace (trace, traceM, traceShow, traceShowM)
import Data.Maybe (catMaybes, mapMaybe, fromMaybe)
import GHC.Real (Ratio((:%)))
import GHC.Exts (IsList)

{-| Take a slice from the given string

>>> slice 1 2 [1, 2, 3, 4, 5]
[2,3]

>>> slice 0 0 [1, 2, 3, 4, 5]
[1]
-}
slice :: Int -> Int -> [a] -> [a]
slice from to = take (to - from + 1) . drop from

-- | body must change "m" and cond should be the function to read information from "m"
while :: MonadState t m => (t -> Bool) -> m a -> m ()
while cond body = do
  info <- get
  when (cond info) $ do { body; while cond body }

-- | a more general version, while users must convert the enviroment to Bool by themselves
whileM :: Monad m => m Bool -> m a -> m ()
whileM cond body = do
  b <- cond
  when b $ do { body; whileM cond body }

-- | a "for" function mimic C style, but no initial value -- as there cannot generally create local variables
-- for (_; cond; post) body
cfor :: MonadState t m => (t -> Bool) -> m a1 -> m a2 -> m ()
cfor testCond post body =
  while testCond $ do { body; post }

{-| a more general "for" function mimics C style

while users should convert the given context to Bool by themselves
-}
cforM :: Monad m => m Bool -> m () -> m b -> m ()
cforM cond post body =
  whileM cond $ do { body; post }

{-| get unique elements in the list, the order will not be maintained

>>> unique [1,1,2,4,2,5,6]
[6,5,4,2,1]
prop> withMaxSuccess 100000 $ \(l :: [Int]) -> toTestUnique l
+++ OK, passed 100000 tests.
--
toTestUnique :: Ord a => [a] -> Bool
toTestUnique l = and $ do
  let lst = unique l
  i <- [0..length lst - 1]
  let (f, ~(h:s)) = splitAt i lst
  return $ h `notElem` (f ++ s)
-}
unique :: Ord a => [a] -> [a]
unique [] = []
unique lst = let ~(h:l) = sort lst in inner [h] l where
  inner :: Eq a => [a] -> [a] -> [a]
  inner l [] = l
  inner ~l@(h:_) (h':rst) = inner (if h == h' then l else h' : l) rst

untilM :: Monad m => (m b -> m Bool) -> (m b -> m b) -> m b -> m b
untilM cond next init = do
  b <- cond init
  if b then init else untilM cond next (next init)

-- prop> withMaxSuccess 1000000 $ \(n :: Int) (l :: [Int]) -> lenEq n l == (n == length l)
-- +++ OK, passed 1000000 tests.
lenEq :: (Eq t, Num t) => t -> [a] -> Bool
lenEq 0 [] = True
lenEq 0 _  = False
lenEq _ [] = False
lenEq n (_:rst) = lenEq (n - 1) rst

-- prop> withMaxSuccess 1000000 $ \(n :: Int) (l :: [Int]) -> lenGt n l == (n > length l)
-- +++ OK, passed 1000000 tests.
lenGt :: (Ord t, Num t) => t -> [a] -> Bool
lenGt n [] = n > 0
lenGt n (_:rst) = lenGt (n - 1) rst

-- prop> withMaxSuccess 1000000 $ \(n :: Int) (l :: [Int]) -> lenGe n l == (n >= length l)
-- +++ OK, passed 1000000 tests.
lenGe :: (Num t, Ord t) => t -> [a] -> Bool
lenGe n [] = n >= 0
lenGe n (_:rst) = lenGe (n - 1) rst

-- prop> withMaxSuccess 1000000 $ \(n :: Int) (l :: [Int]) -> lenLe n l == (n <= length l)
-- +++ OK, passed 1000000 tests.
lenLe :: (Ord t, Num t) => t -> [a] -> Bool
lenLe n lst = not $ lenGt n lst

-- prop> withMaxSuccess 1000000 $ \(n :: Int) (l :: [Int]) -> lenLt n l == (n < length l)
-- +++ OK, passed 1000000 tests.
lenLt :: (Num t, Ord t) => t -> [a] -> Bool
lenLt n lst = not $ lenGe n lst

-- | Binary Division to find the target value
binaryDivision :: Integral a => (a, a) -> (a -> Ordering) -> (Maybe a -> p) -> p
binaryDivision (min, max) test wrapper =
  if min > max then wrapper Nothing else
  let guess = (min + max) `div` 2 in
  case test guess of
    EQ -> wrapper $ Just guess
    LT -> binaryDivision (min, guess - 1) test wrapper
    GT -> binaryDivision (guess + 1, max) test wrapper

{-| Returns all permutation of the given list

>>> arrange [1, 2, 3]
[[1,2,3],[2,1,3],[2,3,1],[1,3,2],[3,1,2],[3,2,1]]
-}
arrange :: [a] -> [[a]]
arrange [] = [[]]
arrange (h:lst) =
  let arlst = arrange lst in do
  lst <- arlst
  n <- [0..length lst]
  let (pre, post) = splitAt n lst
  return $ pre ++ (h:post)


{-| Usual enlarge of the array with new length, if new length <= original length, just return the original one -}
enlargeArray :: (MArray a e m, Ix i, Enum i, Num i) => a i e -> i -> m (a i e)
enlargeArray arr newLen = do
  (min, max) <- getBounds arr
  let lenVec = max - min + 1
  if newLen <= lenVec then return arr
  else do
    newArr <- newArray_ (min, newLen - 1)
    forM_ [min..max] $ \idx -> do
      val <- readArray arr idx
      writeArray newArr idx val
    return newArr

factorial :: (Ord p, Num p) => p -> p
factorial n
  | n <= 1 = 1
  | otherwise = n * factorial (n - 1)

diff :: (Foldable t, Eq b) => [b] -> t b -> [b]
diff l1 l2 = do
  e <- l1
  if e `elem` l2 then [] else return e

whenM :: Monad m => m Bool -> m () -> m ()
whenM cond body = do
  val <- cond
  when val body

-- | empty or just a list of [] is also a valid matrix
isMatrix :: [[a]] -> Bool
isMatrix matrix =
  null matrix ||
  let columnLen = length $ head matrix in and $ lenEq columnLen <$> tail matrix

isNonEmptyMatrix :: [[a]] -> Bool
isNonEmptyMatrix matrix =
  not (null matrix || null (head matrix)) && isMatrix matrix

-- an unsafe function, please make sure matrix is non-empty
getMatrixShape :: [[a]] -> (Int, Int)
getMatrixShape matrix = (length matrix, length $ head matrix)

nonEmptyWithDefault :: Foldable t => (t a -> p) -> p -> t a -> p
nonEmptyWithDefault f def lst =
  if null lst then def else f lst

{-| get a lexical parsing stream

>>> lexicalStream lex "1=>2"
["1","=>","2"]
-}
lexicalStream :: Foldable t => (t a1 -> [(a2, t a1)]) -> t a1 -> [a2]
lexicalStream lex str =
  if null str then [] else
  let ~((hd, tl):_) = lex str in
  hd : lexicalStream lex tl

-- | O(n^2)
isUniqueList :: Eq a => [a] -> Bool
isUniqueList = \case
  []    -> True
  hd:tl -> hd `notElem` tl && isUniqueList tl

-- | O(n log n)
isUniqueOrdLst :: Ord a => [a] -> Bool
isUniqueOrdLst lst = length (unique lst) == length lst

quote :: String -> String
quote str = "\"" ++ str ++ "\""

quoteWith :: String -> String -> String
quoteWith l = quoteWith (splitAt (length l `div` 2) l)
  where
    quoteWith :: (String, String) -> String -> String
    quoteWith (begin, end) str = begin ++ str ++ end

-- | for readability, mark things as impossible, a less conspicuous mark
impossible :: a
impossible = undefined

-- | for readability, mark things as impossible, a more conspicuous mark
eIMPOSSIBLE :: a
eIMPOSSIBLE = undefined

loop :: (Num n, Enum n) => n -> a -> (a -> a) -> a
loop n init func = foldr (const func) init [1..n]

class (Monad m) => Modifiable m r | m -> r where
  newRef :: a -> m (r a)
  readRef :: r a -> m a
  writeRef :: r a -> a -> m ()
  modifyRef :: r a -> (a -> a) -> m ()
  modifyRef ref f = do
    v <- readRef ref
    writeRef ref $ f v

infix 0 <<-
-- | The infix synonym of `writeRef`
(<<-) :: Modifiable m r => r a -> a -> m ()
(<<-) = writeRef

instance Modifiable IO IORef where
  newRef :: a -> IO (IORef a)
  newRef = newIORef
  readRef :: IORef a -> IO a
  readRef = readIORef
  writeRef :: IORef a -> a -> IO ()
  writeRef = writeIORef

instance Modifiable (ST s) (STRef s) where
  newRef :: a -> ST s (STRef s a)
  newRef = newSTRef
  readRef :: STRef s a -> ST s a
  readRef = readSTRef
  writeRef :: STRef s a -> a -> ST s ()
  writeRef = writeSTRef

instance (Monad m) => Modifiable (STT.STT s m) (STT.STRef s) where
  newRef :: Monad m => a -> STT.STT s m (STRef s a)
  newRef = STT.newSTRef
  readRef :: Monad m => STRef s a -> STT.STT s m a
  readRef = STT.readSTRef
  writeRef :: Monad m => STRef s a -> a -> STT.STT s m ()
  writeRef = STT.writeSTRef

minimumWith :: (Foldable t1, Ord a) => (t2 -> a) -> t1 t2 -> t2
minimumWith f = minimumBy $ \a b -> compare (f a) (f b)

swap :: (b, a) -> (a, b)
swap (a, b) = (b, a)

(|>) :: t1 -> (t1 -> t2) -> t2
x |> f = f x

infixl 0 |>

-- | a slightly tighter version of ($) used in the case for special connectors like (|>)
($$) :: (t1 -> t2) -> t1 -> t2
f $$ x = f x

infixr 1 $$

sndMap :: (t -> b) -> (a, t) -> (a, b)
sndMap f (a, b) = (a, f b)

fstMap :: (t -> a) -> (t, b) -> (a, b)
fstMap f (a, b) = (f a, b)

pairMap :: (t1 -> a, t2 -> b) -> (t1, t2) -> (a, b)
pairMap (fa, fb) (a, b) = (fa a, fb b)

bothMap :: (t -> b) -> (t, t) -> (b, b)
bothMap f (a, b) = (f a, f b)

reduceListM :: Monad m => (a -> a -> m a) -> [m a] -> m a
reduceListM foldFunc ~(h:lst) = do
  init <- h
  foldM (\a ma -> do na <- ma; foldFunc a na) init lst

-- | g `compose2` f = \\x y -> g (f x y)
compose2 :: (b -> c) -> (a1 -> a2 -> b) -> a1 -> a2 -> c
compose2 = (.) . (.)

{-| Aggregate according to a feature of the list elements, order is not preserved

Complexity: O(n log_2 n)

>>> aggregateOrdList id [(1, 2), (1, 3), (1, 4), (2, 7), (2, 9)]
[(1,[4,3,2]),(2,[9,7])]
-}
aggregateOrdList :: Ord b1 => (a -> (b1, b2)) -> [a] -> [(b1, [b2])]
aggregateOrdList divFunc lst =
  let l = sortOn (fst . divFunc) lst in
  case l of
    [] -> []
    x:xs ->
      let (a, b) = divFunc x in
      aggregateOrdList a [b] xs
  where
    aggregateOrdList feature acc [] = [(feature, acc)]
    aggregateOrdList feature acc (x:xs) =
      let (a, b) = divFunc x in
      if feature == a then aggregateOrdList a (b:acc) xs
      else (feature, acc) : aggregateOrdList a [b] xs

mapToList :: HashMap.HashTable s k v -> ST s [(k, v)]
mapToList = flip HashMap.foldM [] $ \accLst el -> return $ el : accLst

-- >>> aggregateByHash id [(1, 2), (1, 3), (1, 4), (2, 7), (2, 9)]
-- [(2,[9,7]),(1,[4,3,2])]
aggregateByHash :: (Foldable t, Eq k, Hashable k) => (p -> (k, a)) -> t p -> [(k, [a])]
aggregateByHash divFunc lst = runST $ do
  -- create the hash map
  map <- HashMap.new
  -- add to the map by the first element of `divFunc`
  forM_ lst $ \el ->
    let (feature, ele) = divFunc el in
    HashMap.mutate map feature $ \case
      Just lst -> (Just $ ele : lst, ())
      Nothing  -> (Just [ele], ())
  -- convert the map to list
  mapToList map

{-| Aggreate according to a feature of the list elements, order is preserved, slower than order list version

Complexity: O(n^2)

>>> aggregateList id [(1, 2), (1, 3), (1, 4), (2, 7), (2, 9)]
[(1,[2,3,4]),(2,[7,9])]
-}
aggregateList :: Eq t => (a1 -> (t, a2)) -> [a1] -> [(t, [a2])]
aggregateList divFunc lst =
  aggregatePairList $ divFunc <$> lst
  where
    collectFeature :: (Eq t) => t -> [a] -> [(t, a)] -> ([a], [(t, a)])
    collectFeature _ acc [] = (acc, [])
    collectFeature a acc (x@(a',b'):xs)
      | a == a'   = collectFeature a (b':acc) xs
      | otherwise = sndMap (x:) $ collectFeature a acc xs

    aggreateFirstClass :: (Eq t) => [(t, a)] -> ((t, [a]), [(t, a)])
    aggreateFirstClass ~((a,b):xs) =
      fstMap ((a,) . reverse) $ collectFeature a [b] xs

    aggregatePairList :: (Eq t) => [(t, a)] -> [(t, [a])]
    aggregatePairList []  = []
    aggregatePairList lst =
      let (hdPart, rstLst) = aggreateFirstClass lst in
      hdPart : aggregatePairList rstLst

-- | A quick method to get the unique results
--   FOR FINITE LIST ONLY
--   will maintain the same order, only remove the later appearance of the same element
-- >>> uniqueByHash [1, 2, 1, 9, 7, 2, 3, 2]
-- [1,2,9,7,3]
uniqueByHash :: (Hashable x, Eq x) => [x] -> [x]
uniqueByHash lst = reverse $ runST $ do
  map <- HashMap.new
  foldM (folderM map) [] lst
  where
    folderM map ret ele = do
      maybeV <- HashMap.lookup map ele
      case maybeV of
        Just () -> return ret
        Nothing -> do
          HashMap.insert map ele ()
          return $ ele : ret

-- >>> countByHash [1, 2, 1, 9, 7, 2, 3, 2]
-- [(9,1),(7,1),(3,1),(2,3),(1,2)]
countByHash :: (Hashable x, Eq x, Num n) => [x] -> [(x, n)]
countByHash lst = runST $ do
  map <- HashMap.new
  foldM_ (folderM map) () lst
  HashMap.foldM ((return .) . flip (:)) [] map
  where
    folderM map _ ele =
      HashMap.mutate map ele $ \case
        Just num -> (return $ num + 1, ())
        Nothing  -> (return 1, ())

fetchFromEither :: Either a a -> a
fetchFromEither = \case
  Left  l -> l
  Right r -> r

printSeq :: Show x => String -> [x] -> String
printSeq _sep [] = ""
printSeq _sep [ x ] = show x
printSeq sep (x : lst) = show x ++ sep ++ printSeq sep lst

concatStr :: String -> [String] -> String
concatStr _sep [] = ""
concatStr _sep [ x ] = x
concatStr sep (x : lst) = x ++ sep ++ concatStr sep lst

class Unwrap w where
  -- | A PARTIAL FUNCTION TO GET THE CONTENT OUT
  unwrap :: w t -> t

instance Unwrap Maybe where
  unwrap :: Maybe t -> t
  unwrap ~(Just x) = x
instance Unwrap (Either a) where
  unwrap :: Either a t -> t
  unwrap ~(Right r) = r
instance Unwrap [] where
  unwrap :: [t] -> t
  unwrap ~[x] = x

-- | The same as `show` except that when apply to `String` itself, there is no quote
class ToString s where
  toString :: s -> String

instance Show s => ToString s where
  toString :: Show s => s -> String
  toString = show

instance ToString String where
  toString :: String -> String
  toString = id

-- >>> allCombinations [1, 2, 3]
-- [[1,2,3],[1,2],[1,3],[1],[2,3],[2],[3],[]]
allCombinations :: [a] -> [[a]]
allCombinations [] = [[]]
allCombinations (x : l) =
  let lst = allCombinations l in
  fmap (x:) lst ++ lst

cartesianProduct :: [[a]] -> [[a]]
cartesianProduct [] = [[]]
cartesianProduct (x:xs) = [ y:ys | y <- x, ys <- cartesianProduct xs ]
