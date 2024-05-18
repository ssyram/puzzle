{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
module NewShortStuff where

import MyData.Array
import qualified Data.HashTable.ST.Basic as HT
import Utils (eIMPOSSIBLE, bothMap, Modifiable (newRef, readRef), whenM, (<<-))
import Data.List (sort, partition)
import Test.QuickCheck (quickCheckWith, quickCheck, withMaxSuccess, Arbitrary (arbitrary))
import Debug.Trace (trace)
import qualified Control.Monad as List
import Control.Monad
import Control.Monad.Cont (ContT(runContT), MonadCont (callCC))
import Data.Hashable (Hashable)
import Control.Monad.Trans.Cont (evalContT)
import Control.Monad.ST (ST)
import Control.Monad.ST.Strict (runST)
import Control.Monad.ST.Class (liftST)
import qualified Data.Maybe as Maybe
import qualified MyData.Vector as V

mergeTwoSorted :: Ord a => [a] -> [a] -> [a]
mergeTwoSorted l [] = l
mergeTwoSorted [] l = l
mergeTwoSorted l1@(x:l1') l2@(y:l2')
  | x < y     = x:mergeTwoSorted l1' l2
  | otherwise = y:mergeTwoSorted l1 l2'


findNthSorted_correct :: Ord a => Int -> Array a -> Array a -> Maybe a
findNthSorted_correct n l1 l2 =
  fromList (mergeTwoSorted (toList l1) $ toList l2) !? n

-- 10,000,000 TEST PASSED
findNthSorted :: Ord e => Int -> Array e -> Array e -> Maybe e
findNthSorted n l1 l2
  | n < 0 = Nothing
  | isEmpty l1 && isEmpty l2 = Nothing
  | n >= size l1 + size l2 = Nothing
  | size l1 < size l2 = compute l1 l2
  | otherwise = compute l2 l1
  where
    compute l1 l2
      | startPoint > size l1 = error $ "Error at start point -- it is more than size of l1, start point = " ++ show startPoint
      | otherwise =
        Just $ loop startPoint (size l1)
      where
        startPoint = max 0 $ n + 1 - size l2
        loop iMin iMax
          | iMin > iMax = error "Invalid"
          -- see if the plate should be moved
          -- additional case to handle: when `i > n + 1` it means undoubtedly the plate is too right
          | i > n + 1 = loop iMin (i - 1)
          -- otherwise, test if the plate is correct
          | i < size l1 && j > 0 && l1 ! i < l2 ! (j - 1) = loop (i + 1) iMax
          | i > 0 && j < size l2 && l1 ! (i - 1) > l2 ! j = loop iMin (i - 1)
          -- otherwise, it is pinpointed, just need to find the point
          | i == 0 = l2 ! (j - 1)
          | j == 0 = l1 ! (i - 1)
          | otherwise = max (l1 ! (i - 1)) (l2 ! (j - 1))
          where i = (iMin + iMax) `div` 2
                j = n + 1 - i

-- prop> testFindNthSorted
testFindNthSorted :: Int -> [Int] -> [Int] -> Bool
testFindNthSorted n l1 l2 =
  -- trace (concat
  --   [ "n = "
  --   , show n
  --   , "; l1 = "
  --   , show l1
  --   , "; l2 = "
  --   , show l2 ]
  -- ) $ 
  let a1 = fromList $ sort l1
      a2 = fromList $ sort l2 in
  findNthSorted n a1 a2 == findNthSorted_correct n a1 a2

-- >>> findLstNthSorted 0 [0] [-1]
-- Just 0
findLstNthSorted :: Ord e => Int -> [e] -> [e] -> Maybe e
findLstNthSorted n l1 l2 =
  let a1 = fromList $ sort l1
      a2 = fromList $ sort l2 in
  findNthSorted n a1 a2

-- test passed
runTestFindNthSorted :: IO ()
runTestFindNthSorted = quickCheck $ withMaxSuccess 10000000 testFindNthSorted


-- | Every acyclic directed graph can be represented as [Node x]
data Node x = Node x [Node x]

htInsertIfNotExist :: (Eq k, Hashable k) => HT.HashTable s k a -> k -> a -> ST s Bool
htInsertIfNotExist ht x v = do
  HT.mutate ht x $ \case
     Nothing -> (Just v, True)
     Just v' -> (Just v', False)

topoSort :: (Eq a, Hashable a) => [Node a] -> [a]
topoSort lst = runST $ do
  visited <- HT.new
  zrDegNodes <- findZeroDegree lst
  List.foldM (dfs visited) [] zrDegNodes
  where
    findZeroDegree lst = do
      pointedTo <- HT.new
      forM_ lst $ \(Node _ lst) ->
        forM_ lst $ \(Node x _) -> HT.insert pointedTo x ()
      flip List.filterM lst $ \(Node x _) -> do
        v <- HT.lookup pointedTo x
        return $ Maybe.isNothing v

    dfs visited acc (Node x lst) = evalContT $ callCC $ \ret -> do
      exists <- liftST $ htInsertIfNotExist visited x ()
      when exists $ ret acc
      acc' <- liftST $ List.foldM (dfs visited) acc lst
      return $ x : acc'

data Nat = Zero | Succ Nat

data family Vec (n :: Nat) a

data instance Vec Zero a where
  VNil :: Vec Zero a

data instance Vec (Succ n) a where
  VCons :: a -> Vec n a -> Vec (Succ n) a

data GenVec (n :: Nat) a where
  GVNil :: GenVec Zero a
  GVCons :: a -> GenVec n a -> GenVec (Succ n) a

-- >>> quickSort [0]
-- [0]
quickSort :: Ord a => [a] -> [a]
quickSort [] = []
quickSort (x : lst) =
  let (s, l) = partition (<= x) lst
  in quickSort s ++ [x] ++ quickSort l


-- | Base model:
-- for (int i = 0; i < len; ++i)
--   for (int j = i + 1; j < len; ++j)
--     if (lst[i] > lst[j]) swap(lst, i, j);
-- >>> selectSort [0]
-- [0]
selectSort :: Ord b => [b] -> [b]
selectSort l = runST $ do
  let len = fromIntegral $ length l
  v <- V.fromList l
  forM_ [0..len-1] $ \i ->
    forM_ [i+1..len-1] $ \j -> do
      ~(Just ei) <- V.readAt v i
      ~(Just ej) <- V.readAt v j
      when (ei > ej) $ do
        V.writeAt v i ej
        V.writeAt v j ei
        return ()
  V.toList v

-- | Base model:
-- for (int i = 0; i < len; ++i)
--   for (int j = 0; j < len - i - 1; ++j)
--     if (lst[j] > lst[j+1]) swap(lst, j, j+1);
bubbleSort :: Ord b => [b] -> [b]
bubbleSort l = runST $ do
  let len = fromIntegral $ length l
  v <- V.fromList l
  forM_ [0..len-1] $ \i ->
    forM_ [0..len-i-2] $ \j -> do
      ~(Just ej) <- V.readAt v j
      ~(Just ejp1) <- V.readAt v $ j + 1
      when (ej > ejp1) $ do
        V.writeAt v j ejp1
        V.writeAt v (j + 1) ej
        return ()
  V.toList v

mergeSort :: Ord a => [a] -> [a]
mergeSort [] = []
mergeSort [x] = [x]
mergeSort lst = uncurry merge $ bothMap mergeSort $ div2 lst
  where
    div2 lst = splitAt (length lst `div` 2) lst
    merge l [] = l
    merge [] l = l
    merge l1@(x:l1') l2@(y:l2')
      | x > y     = y:merge l1 l2'
      | otherwise = x:merge l1' l2


mkHeap :: Ord a => V.Vector s a -> Integer -> Integer -> ST s ()
mkHeap arr bound rootIdx = do
  let i = rootIdx
  largest <- newRef rootIdx
  let left = 2 * i + 1
  let right = 2 * i + 2
  whenM (swapHold largest left) (largest <<- left)
  whenM (swapHold largest right) (largest <<- right)
  whenM ((/= i) <$> readRef largest) $ do
    swap largest i
    largest <- readRef largest
    mkHeap arr bound largest
  where
    swapHold largestRef idx
      | idx >= bound = return False
      | otherwise = do
        largest <- readRef largestRef
        ~(Just arrLargest) <- V.readAt arr largest
        ~(Just arrIdx) <- V.readAt arr idx
        return $ arrIdx > arrLargest
    swap largestRef idx = do
      largest <- readRef largestRef
      ~(Just arrLargest) <- V.readAt arr largest
      ~(Just arrIdx) <- V.readAt arr idx
      V.writeAt arr largest arrIdx
      V.writeAt arr idx arrLargest



-- prop> withMaxSuccess 1000 quickTestSort
-- +++ OK, passed 1000 tests.
quickTestSort :: [Int] -> Bool
quickTestSort (l :: [Int]) =
  let bs = bubbleSort l
      ss = selectSort l
      qs = quickSort l
      ms = mergeSort l
  in bs == ss && ss == qs && qs == ms



------------------------------ Median of Two Equal-Length Sorted List ------------------------------

medianOfTwoEqLenSorted :: (Ord e, Num e) => Array e -> Array e -> e
medianOfTwoEqLenSorted l1 l2 = find (0, size l1)
  where
    len = size l1
    find (iMin, iMax)
      | iMin > iMax = error "Empty Input"
      | i > 0 && l1 ! (i - 1) > l2 ! j = find (iMin, i - 1)
      | i < len && l1 ! i < l2 ! (j - 1) = find (i + 1, iMax)
      | i == 0 = l2 ! (j - 1)
      | j == 0 = l1 ! (i - 1)
      | otherwise = max (l1 ! (i - 1)) (l2 ! (j - 1))
      where i = (iMin + iMax) `div` 2
            j = len - i

newtype SortedEqLenLstPair x = SortedEqLenLstPair (Array x, Array x)
  deriving (Eq, Ord, Show)

instance (Ord x, Arbitrary x) => Arbitrary (SortedEqLenLstPair x) where
  arbitrary = do
    p1 <- arbitrary
    hd <- arbitrary
    let l1 = hd : p1
    l2 <- forM l1 $ const arbitrary
    return $ SortedEqLenLstPair (fromList $ sort l1, fromList $ sort l2)

-- prop> withMaxSuccess 10000 testMedian
-- +++ OK, passed 10000 tests.
testMedian :: SortedEqLenLstPair Int -> Bool
testMedian (SortedEqLenLstPair (l1, l2)) =
  medianOfTwoEqLenSorted l1 l2 == Maybe.fromJust (findNthSorted_correct (size l1 - 1) l1 l2)



--------------------------------- Simpler Z List Computation ---------------------------------

-- | Compute the Z list for a given list -- the head is `0`
--   and for each `i` greater than 0, it means the length of the matching sub-string
-- >>> computeZList [1, 2, 3, 1, 2, 1, 2, 3, 1, 4, 3, 4]
-- [0,0,0,2,0,4,0,0,1,0,0,0]
computeZList :: Eq e => [e] -> [Int]
computeZList lst = runST $ do
  lst <- return $ fromList lst
  let len = size lst
  zv <- V.newWithSize 0 len

  foldM_ (wrap zv lst) (0, 0, 0) [1..len-1]

  V.toList zv
  where
    -- | A pure helper function to mark the final return value
    wrap zv lst (_, l, r) idx = do
      ret@(val,_,_) <- compute zv lst (l, r) idx
      V.writeAt zv idx val
      return ret

    -- | Perform the actual key computation
    --   Value `r` points to after the matching point
    compute zv lst (l, r) idx
      -- if `idx >= r` then it means we must start matching from this point
      | idx >= r = do
        let r = matchFrom lst 0 idx
        return (r - idx, idx, r)
      | otherwise = do
        ~(Just lenHi) <- V.readAt zv (idx - l)
        if lenHi + idx <= r then return (lenHi, l, r)
        else do
          r <- return $ matchFrom lst (r - l) r
          return (r - idx, idx, r)

-- | from `hd` and `r` match and returns 1 + the final match place
matchFrom :: Eq e => Array e -> Int -> Int -> Int
matchFrom lst hd r
  | r >= size lst || lst ! hd /= lst ! r = r
  | otherwise = matchFrom lst (hd + 1) (r + 1)

-- >>> checkZList [1, 2, 3, 1, 2, 1, 2, 3, 1, 4, 3, 4] [0,0,0,2,0,4,0,0,1,0,0,0]
-- True
checkZList :: Eq e => [e] -> [Int] -> Bool
checkZList lst zLst
  | length lst /= length zLst = False
  | null lst && null zLst = True
  | head zLst /= 0 = False
  | otherwise = all (ok $ fromList lst) $ zip [1..] $ tail zLst
  where ok lst (idx, matchLen) = matchFrom lst 0 idx - idx == matchLen

-- prop> withMaxSuccess 100000 quickTestZList
-- +++ OK, passed 100000 tests.
quickTestZList :: [Int] -> Bool
quickTestZList l = checkZList l $ computeZList l









------------------------------------ Manacher ------------------------------------

-- | Returns the list `l` where `l[i]` means from this index `i`
--   what is the longest palindrome from this center
--   CONSIDER also the STAKE POSITIONS
-- >>> manacherPalindrome [1,2,2,1]
-- [0,1,0,1,4,1,0,1,0]
manacherPalindrome :: Eq a => [a] -> [Int]
manacherPalindrome lst = runST $ do
  lst <- return $ fromList $ addManacherStake lst
  let len = size lst
  zv <- V.newWithSize 0 len

  foldM_ (wrap lst zv) (0, 0, 0) [1..len-1]

  V.toList zv
  where
    wrap lst zv (_, c, r) idx = do
      ret@(v,_,_) <- compute lst zv (c, r) idx
      V.writeAt zv idx v
      return ret

    compute lst zv (c, r) idx
      | idx >= r = do
        let r = matchPalindromeFrom lst idx (idx + 1)
        return (r - idx - 1, idx, r)
      | otherwise = do
        ~(Just vCl) <- V.readAt zv (2 * c - idx)
        if idx + vCl < r - 1 then return (vCl, c, r)
        else do
          r <- return $ matchPalindromeFrom lst idx r
          return (r - idx - 1, idx, r)
    
addManacherStake :: [a] -> [Maybe a]
addManacherStake lst = do { x <- lst; [Nothing, Just x] } ++ [Nothing]

matchPalindromeFrom :: Eq e => Array e -> Int -> Int -> Int
matchPalindromeFrom lst center right
  | right >= size lst                         = right
  | 2 * center - right < 0                    = right
  | lst ! (2 * center - right) /= lst ! right = right
  | otherwise = matchPalindromeFrom lst center (right + 1)

longestPalindromeByManacher :: Eq a => [a] -> Int
longestPalindromeByManacher l = maximum $ manacherPalindrome l

correctPalindromeList :: Eq a => [a] -> [Int]
correctPalindromeList l =
  let lst = addManacherStake l
      arr = fromList lst
  in flip map [0..size arr-1] $ \idx ->
    let r = matchPalindromeFrom arr idx (idx + 1) in
    r - idx - 1

-- prop> withMaxSuccess 100000 quickTestPalindromeList
-- +++ OK, passed 100000 tests.
quickTestPalindromeList :: [Int] -> Bool
quickTestPalindromeList l = manacherPalindrome l == correctPalindromeList l




-------------------------------------- Shortest Path --------------------------------------



