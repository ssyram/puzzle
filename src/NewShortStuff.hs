{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -fno-defer-type-errors #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE InstanceSigs #-}
module NewShortStuff where

import MyData.Array
import qualified Data.HashTable.ST.Basic as HT
import Utils (eIMPOSSIBLE, bothMap, Modifiable (newRef, readRef, writeRef, modifyRef), whenM, (<<-), (|>), slice, whileM, factorial, fstMap, isMatrix, lenEq, orM, andM, toLogicT)
import Data.List (sort, partition, isPrefixOf, (\\))
import Test.QuickCheck (quickCheckWith, quickCheck, withMaxSuccess, Arbitrary (arbitrary), frequency, shuffle)
import Debug.Trace (trace)
import qualified Control.Monad as List
import Control.Monad
import Control.Monad.Cont (ContT(runContT), MonadTrans (lift))
import Data.Hashable (Hashable)
import Control.Monad.Trans.Cont (evalContT, callCC, evalCont, shift, shiftT)
import Control.Monad.ST (ST)
import Control.Monad.ST.Strict (runST)
import Control.Monad.ST.Class (liftST, MonadST (World))
import qualified Data.Maybe as Maybe
import qualified MyData.Vector as V
import qualified Data.Map as M
import Data.Maybe (fromMaybe, isJust, fromJust)
import Control.Monad.Trans.Writer (WriterT(runWriterT), runWriter)
import Control.Monad.Writer (MonadWriter(tell, listen, pass))
import Control.Monad.State.Strict (execStateT, MonadState, modify', evalStateT, execState)
import qualified Data.HashSet as S
import Control.Monad.Identity
import qualified Data.Set as IS
import qualified Data.Vector as DV
import qualified Data.Vector.Mutable as DVM
import Control.Monad.Trans.Except (runExceptT)
import qualified ShortStuff
import qualified Data.Array.IO as IOArray
import qualified Data.Array.IO.Safe as IOA
import qualified Data.Vector.Unboxed as DVU
import qualified DataStructure.RBTree as RBT
import Control.Applicative (Applicative(..), Alternative ((<|>)))
import Data.Functor (($>))
import qualified Data.Sequence as Seq
import qualified Control.Monad.Logic as L
import qualified TryLogict as L


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
      | startPoint > size l1 = 
        error $ 
          "Error at start point -- it is more than size of l1, start point = " ++ 
          show startPoint
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




-------------------------------------- Merge K Sorted List --------------------------------------

mergeKSortedList :: (Foldable t, Ord a) => t [a] -> [a]
mergeKSortedList lst =
  let pq = foldl addToPriQ M.empty lst in
  reverse $ loop [] pq
  where
    addToPriQ pq [] = pq
    addToPriQ pq (x:lst) = M.alter (add lst) x pq
      where add lst = Just . (lst:) . fromMaybe []

    loop acc pq = case M.minViewWithKey pq of
      Nothing -> acc
      Just ((x, mat), pq) ->
        -- add the length of `mat` times `x` to `acc`, indicating the number of appearance of `x`
        let acc' = foldr (const (x:)) acc mat in
        loop acc' $ foldl addToPriQ pq mat


mergeKSortedList_correct :: (Foldable t, Ord a) => t [a] -> [a]
mergeKSortedList_correct = foldr mergeTwoSorted []

newtype SortedList x = SortedList [x]

instance Show x => Show (SortedList x) where
  show (SortedList xs) = show xs

instance (Arbitrary x, Ord x) => Arbitrary (SortedList x) where
  arbitrary = SortedList . sort <$> arbitrary


-- prop> withMaxSuccess 10000 $ checkMergeKSortedLists
-- +++ OK, passed 10000 tests.
checkMergeKSortedLists :: [SortedList Int] -> Bool
checkMergeKSortedLists lst =
  let l = fmap (\(SortedList l) -> l) lst in
  mergeKSortedList l == mergeKSortedList_correct l



----------------------------------- Longest Valid Parentheses -----------------------------------

longestValidParentheses :: (Ord a, Num a, Enum a) => [Char] -> a
longestValidParentheses paren = fst $ foldl compute (0, [-1]) $ zip [0..] paren
  where compute (maxLen, stk) (idx, c)
          | c == '('  = (maxLen, idx:stk)
          | c == ')'  = case tail stk of  -- pop first
            []       -> (maxLen, [idx])   -- reaches the bottom, meaning this an extra symbol ')'
            pIdx:stk -> (max maxLen (idx - pIdx), pIdx:stk)
          | otherwise = error $ "UNKNOWN CHARACTER: " ++ [c]

dblTraverseLngstVldParentheses :: (Foldable t, Num a, Ord a) => t Char -> a
dblTraverseLngstVldParentheses paren =
  max (maxLRScan paren) (maxRLScan paren)
  where
    maxLRScan = extract . foldl computeLR (0, 0, 0)
    maxRLScan = extract . foldr computeRL (0, 0, 0)
    extract (x,_,_) = x
    computeLR (maxLen, l, r) c
      | l' == r'  = (max maxLen (2 * r'), l', r')
      | l' < r'   = (maxLen, 0, 0)
      | otherwise = (maxLen, l', r')
      where (l', r') = updateCount (l, r) c
    computeRL c (maxLen, l, r)
      | l' == r'  = (max maxLen (2 * r'), l', r')
      | l' > r'   = (maxLen, 0, 0)
      | otherwise = (maxLen, l', r')
      where (l', r') = updateCount (l, r) c
    updateCount (l, r) c = case c of
      '('  -> (l + 1, r)
      ')'  -> (l, r + 1)
      _otw -> error $ "UNKNOWN CHARACTER: " ++ [c]

newtype ParenStr = ParenStr [Char]

instance Show ParenStr where
  show (ParenStr s) = s

instance Arbitrary ParenStr where
  arbitrary = ParenStr . fmap toParen <$> arbitrary
    where
      toParen :: Int -> Char
      toParen x = case abs $ x `mod` 2 of
        0 -> '('
        1 -> ')'
        _ -> eIMPOSSIBLE

-- prop> withMaxSuccess 100000 checkValidParen
-- +++ OK, passed 100000 tests.
checkValidParen :: ParenStr -> Bool
checkValidParen (ParenStr lst) =
  longestValidParentheses lst == dblTraverseLngstVldParentheses lst


--------------------------------- Concatenation Substring ---------------------------------

-- >>> substringConcat "barmanfoofoobarthefoobarman" ["bar","foo","the"]
-- [9,12,15]
substringConcat :: (Hashable x, Eq x) => [x] -> [[x]] -> [Int]
substringConcat s lst
  | wordLen <= 0 = []
  | sLen < totalLen = []
  | otherwise    = sort $ runST $ flip execStateT [] $ do
    wordCount <- liftST $ genWordCount lst

    forM_ [0..wordLen-1] $ \initId -> do
      curCount <- liftST HT.new
      loop s wordCount curCount initId initId
      return ()
  where
    sLen = length s
    wordLen = case lst of [] -> 0; hd:_ -> length hd
    totalLen = wordLen * length lst

    addCount count e = liftST $ do
      HT.mutate count e $ \case
        Nothing -> (Just 1, ())
        Just ct -> (Just $ ct + 1, ())

    rmvCount count e = liftST $ do
      HT.mutate count e $ \case
        Nothing -> (Nothing, ())
        Just 1  -> (Nothing, ())
        Just ct -> (Just $ ct - 1, ())

    genWordCount lst = do
      wordCount <- HT.new
      forM_ lst $ addCount wordCount
      return wordCount

    hasCount count e = liftST $ isJust <$> HT.lookup count e

    getCount count e = liftST $ fromMaybe 0 <$> HT.lookup count e

    loop :: (Monad m, MonadST m, Hashable k, Eq k, MonadState [Int] m) =>
      [k] ->
      HT.HashTable (World m) [k] Int ->
      HT.HashTable (World m) [k] Int -> Int -> Int -> m ()
    loop s wordCount curCount left right = evalContT $ callCC $ \ret -> do
      when (right + wordLen > sLen) $ ret ()
      let right' = right + wordLen
          word = slice right (right' - 1) s

      whenM (not <$> hasCount wordCount word) $ do
        new <- liftST HT.new
        v <- lift $ loop s wordCount new right' right'
        ret v

      addCount curCount word

      leftRef <- liftST $ newRef left

      -- Move left forward to erase more count
      whileM ((>) <$> getCount curCount word <*> getCount wordCount word) $ do
        left <- liftST $ readRef leftRef
        let left' = left + wordLen
            wordLeft = slice left (left' - 1) s
        rmvCount curCount wordLeft
        liftST $ writeRef leftRef left'

      left' <- liftST $ readRef leftRef

      -- Mark the found result
      when (right' - left' == totalLen) $ modify' (left':)

      lift $ loop s wordCount curCount left' right'


correctConcateOfWordBags :: String -> [String] -> [Int]
correctConcateOfWordBags str set = do
  (pos, lst) <- [(n, drop n str) | n <- [0..length str - 1]]
  if isValid lst set then return pos else []
  where
    isValid :: String -> [String] -> Bool
    isValid lst set =
      (null set ||) $
      or $ do
        str <- set
        if str `isPrefixOf` lst then return $ isValid (lst \\ str) (set \\ [str])
        else return False



--------------------------------- First Missing Positive Number ---------------------------------

evalCC :: Monad m => ((r -> ContT r m b) -> ContT r m r) -> m r
evalCC f = evalContT $ callCC f

firstMissingPositive_correct :: (Num a, Ord a) => [a] -> a
firstMissingPositive_correct lst =
  foldl (\res n -> if res == n then res + 1 else res) 1 $ sort lst

firstMissingPositive_quick :: (Eq p, Hashable p, Num p) => [p] -> p
firstMissingPositive_quick lst =
  findIdx 1 $ S.fromList lst
  where findIdx n set
          | n `S.member` set = findIdx (n + 1) set
          | otherwise        = n

firstMissintPositive :: Integral a => [a] -> a
firstMissintPositive lst = runST $ do
  arr <- V.fromList lst
  len <- V.len arr
  liftST $ forM_ [0..len - 1] $ seekSwap arr
  evalCC $ \ret -> do
    forM_ [0..len - 1] $ \i -> do
      ~(Just arrI) <- liftST $ V.readAt arr i
      when (arrI /= i + 1) $ do ret $ i + 1; return ()
    ret $ len + 1
  where
    seekSwap arr i = do
      -- arrI == j
      ~(Just j) <- V.readAt arr i
      V.readAt arr (j - 1) >>= \case
        Just arrJm1 | arrJm1 /= j -> do
          V.writeAt arr i arrJm1
          V.writeAt arr (j - 1) j
          seekSwap arr i
        _otw -> return ()



-- prop> withMaxSuccess 100000 $ checkFirstMissingPostive
-- +++ OK, passed 100000 tests.
checkFirstMissingPostive :: [Int] -> Bool
checkFirstMissingPostive (l :: [Int]) =
  [ firstMissintPositive
  , firstMissingPositive_quick
  , firstMissingPositive_correct
  ]
  |> fmap ($l)
  |> allEq
  where allEq [] = True
        allEq (x:lst) = all (==x) lst


---------------------------------- Trapping Water ----------------------------------

{-| Key insight:

  Water trapped at each position is `min maxLeft maxRight - this`.
-}
trapWater_pointer :: (Num a, Ord a) => [a] -> a
trapWater_pointer lst = case lst of
  []  -> 0
  [_] -> 0
  _   -> runST $ do
    vec <- V.fromList lst
    len <- V.len vec
    ~(Just initLeftMax) <- V.readAt vec 0
    ~(Just initRigMax) <- V.readAt vec (len - 1)

    flip execStateT 0 $ loop vec 0 (len - 1) initLeftMax initRigMax
  where
    {- | Loop Invariant:
      vec[left] <  vec[right] -> left_max <  right_max && vec[right] == right_max
      vec[left] >= vec[right] -> left_max >= right_max && vec[left]  == left_max
    -}
    loop vec l r lm rm
      | l == r    = return ()
      | l > r     = eIMPOSSIBLE
      | otherwise = do
        ~(Just lv) <- liftST $ V.readAt vec l
        ~(Just rv) <- liftST $ V.readAt vec r
        if lv < rv then do
          let l' = l + 1
          ~(Just lv') <- liftST $ V.readAt vec l'
          let lm' = max lm lv'
          modify' (+(lm' - lv'))
          loop vec l' r lm' rm
        else do
          let r' = r - 1
          ~(Just rv') <- liftST $ V.readAt vec r'
          let rm' = max rm rv'
          modify' (+(rm' - rv'))
          loop vec l r' lm rm'

trapWater_two :: (Num a, Ord a) => [a] -> a
trapWater_two lst =
  zip3 lm rm lst
  |> fmap (\(lm, rm, this) -> min lm rm - this)
  |> sum
  where
    !lm = scanl1 max lst
    !rm = scanr1 max lst

-- prop> withMaxSuccess 1000000 $ checkTrapWater
-- +++ OK, passed 1000000 tests.
checkTrapWater :: [Int] -> Bool
checkTrapWater (lst :: [Int]) =
  let l = fmap abs lst in
  trapWater_pointer l == trapWater_two l



------------------------------------------ N Queens ------------------------------------------

-- >>> nQueens 4
-- [[3,1,4,2],[2,4,1,3]]
-- >>> length $ nQueens 8
-- 92
nQueens :: Integral t => t -> [[t]]
nQueens n = runST $ do
  -- `True` for `isEmpty`
  colInfo <- V.newWithSize True n
  leftTDInfo <- V.newWithSize True (2 * n)
  rightTDInfo <- V.newWithSize True (2 * n)

  let
    modQueen i j val = liftST $ do
      V.writeAt colInfo j val
      V.writeAt leftTDInfo (n - i + j) val
      V.writeAt rightTDInfo (i + j) val
    addQueen i j = modQueen i j False
    rmvQueen i j = modQueen i j True
    okToAdd i j = liftST $ do
      ~(Just col) <- V.readAt colInfo j
      ~(Just leftTD) <- V.readAt leftTDInfo (n - i + j)
      ~(Just rightTD) <- V.readAt rightTDInfo (i + j)
      return $ col && leftTD && rightTD
    loop acc i
      | i >= n = modify' (reverse acc:)
      | otherwise = do
        forM_ [0..n-1] $ \j ->
          whenM (okToAdd i j) $ do
            addQueen i j
            loop (j + 1:acc) (i + 1)  -- `j + 1` for display purpose
            rmvQueen i j
            return ()

  flip execStateT [] $ loop [] 0

nQueens_nonST :: Integral t => t -> [[t]]
nQueens_nonST n = snd $ runWriter $ loop [] 0
  where
    loop acc i
      | i >= n = tell [acc]
      | otherwise =
        forM_ [0..n-1] $ \j ->
          when (valid acc n i j) $ loop (j+1:acc) (i+1)
    valid acc n i j =
      and [ j' /= j && i + j /= i' + j' && n - i + j /= n - i' + j'
      | (i', j'') <- zip [i-1,i-2..0] acc, let j' = j'' - 1 ]

-- Test Passed
quickTestNQueens :: IO ()
quickTestNQueens = do
  forM_ [0..10] $ \i -> do
    putStrLn $ "Testing: " ++ show i
    when (IS.fromList (nQueens i) /= IS.fromList (nQueens_nonST i)) $ error $ show i
  putStrLn "All test passed."



-------------------------------------- k-th Permutation --------------------------------------

kthPermutation :: Int -> Int -> [Int]
kthPermutation n k = lstPermutation (IS.fromList [1..n]) (factorial n) $ k - 1
  where
    lstPermutation sl fact k
      | IS.null sl = []
      | otherwise =
        let fact' = fact `div` IS.size sl  -- n! / n == (n - 1)!
            (tIdx, k') = k `divMod` fact'
            this = IS.elemAt tIdx sl
            sl' = IS.deleteAt tIdx sl
        in this : lstPermutation sl' fact' k'


-------------------------------------- largestRectangleHistogram --------------------------------------

{-|
Base insight: the width is an element as a base times the maximum width around it.

Key idea: Use stack to store those not yet cleared -- 
  with whom as base, the maximum width may be extended.

Key insight: for two consecutive elements in the stack, [..., i, j, ...]
  then `i` will be the start of the rectangle with base `j` 
Note that:
  while height[i] and height[j] might be of the same height
  in this case, there must be consecutive popping and the right value will be on the final (earliest)
  one -- when popping, it finds the correct left of the whole rectangle.
-}
-- >>> largestRectangleHistogram [2,1,5,6,2,3]
-- 10
-- >>> largestRectangleHistogram [2,4]
-- 4
largestRectangleHistogram :: (Ord b, Num b, Enum b) => [b] -> b
largestRectangleHistogram lst =
  -- postpending 0 to `lst` in order to clear the stack
  snd $ foldl folder ([], 0) $ zip [0..] $ lst ++ [0]
  where
    folder (stk, maxVal) p@(i, h) = fstMap (p:) $ loop stk maxVal
      where
        loop [] maxVal = ([], maxVal)
        loop stk@((_,h'):stk') maxVal
          | h >= h' = (stk, maxVal)
          -- h < h'
          | otherwise =
            let width = case stk' of [] -> i; (i'',_):_ -> i - 1 - i'' in
            loop stk' $ max maxVal $ width * h'


------------------------------------ largestRectangleGraph ------------------------------------

class Dot t where isOn :: t -> Bool

instance Dot String where
  isOn :: String -> Bool
  isOn = \case
    "0" -> False
    "1" -> True
    otr -> error $ "Invalid dot representation: " ++ show otr

instance Dot Char where
  isOn :: Char -> Bool
  isOn = \case
    '0' -> False
    '1' -> True
    otr -> error $ "Invalid dot representation: " ++ show otr

instance Dot Bool where
  isOn :: Bool -> Bool
  isOn = id

-- >>> largestRectangleGraph [["1", "0", "1", "0", "0"],["1", "0", "1", "1", "1"],["1", "1", "1", "1", "1"],["1", "0", "0", "1", "0"]]
-- 6
largestRectangleGraph :: (Num p, Dot t, Ord p, Enum p) => [[t]] -> p
largestRectangleGraph dotGraph
  | not $ isMatrix dotGraph = error "Not a matrix."
  | null dotGraph = 0
  | null $ head dotGraph = 0
  | otherwise = snd $ foldl compute (0 <$ head dotGraph, 0) dotGraph
  where
    compute (prevHeights, maxVal) line =
      let heights = updateHeights prevHeights line
          maxVal' = largestRectangleHistogram heights
      in (heights, max maxVal maxVal')
    updateHeights prevHeights line =
      zip prevHeights line
      |> fmap (\(h, dot) -> if isOn dot then h + 1 else 0)


------------------------------------- Is Scramble String -------------------------------------

scrambleBaseCheck :: (Eq a, Hashable a) => [a] -> [a] -> Maybe Bool
scrambleBaseCheck s l
  | not $ lenEq (length s) l = Just False
  | otherwise = runST $ do
    sMap <- HT.new
    lMap <- HT.new
    forM_ (zip s l) $ \(cs, cl) -> do
      incMap sMap cs
      incMap lMap cl
    b <- cmpMap sMap lMap
    if not b then return $ Just False
    else if length s <= 3 then return $ Just True
    else return Nothing

-- >>> isScrambleString_dynamic "great" "rgeat"
-- True
isScrambleString_dynamic :: (Eq a, Hashable a) => [a] -> [a] -> Bool
isScrambleString_dynamic s l =
  fromMaybe (compute (DV.fromList s) (DV.fromList l)) (scrambleBaseCheck s l)
  where
    initTripMat s l = do
      let n = DV.length s
      DVM.generateM n $ \i ->
        DVM.generateM n $ \j ->
          DVM.generateM (n + 1) $ \case
            0 -> return True
            1 -> return $ s DV.! i == l DV.! j
            _ -> return False

    readTripMat tripMat i j k = do
      lineMat <- DVM.read tripMat i
      col <- DVM.read lineMat j
      DVM.read col k

    writeTripMat tripMat i j k v = do
      lineMat <- DVM.read tripMat i
      col <- DVM.read lineMat j
      DVM.write col k v

    compute s l = runST $ do
      let n = DV.length s
      tripMat <- initTripMat s l

      let get = readTripMat tripMat
          write = writeTripMat tripMat

      forM_ [2..n] $ \k ->
        forM_ [0..n-k] $ \i ->
          forM_ [0..n-k] $ \j ->
            forM_ [1..k-1] $ \l -> do
              v <- orM
                [
                  andM [  -- order match
                    get i j l,
                    get (i + l) (j + l) (k - l)
                  ],
                  andM [  -- reverse match
                    get i (j + k - l) l,
                    get (i + l) j (k - l)
                  ]
                ]
              when v $ write i j k True

      get 0 0 n


incMap map e = liftST $ HT.mutate map e $ \case
  Nothing -> (Just 1, ())
  Just c -> (Just $ c + 1, ())

cmpMap map1 map2 =
  liftST $ andM [
    (==) <$> HT.size map1 <*> HT.size map2,
    HT.foldM (cmpFold map2) True map1
  ]

cmpFold map res (k, v) =
  if not res then return False
  else HT.lookup map k >>= \case
    Nothing -> return False
    Just v' -> return $ v == v'

-- >>> isScrambleString_frequency "great" "rgeat"
-- True
-- >>> isScrambleString_frequency "abcde" "caebd"
-- False
isScrambleString_frequency :: (Hashable a, Eq a) => [a] -> [a] -> Bool
isScrambleString_frequency s l =
  fromMaybe (runST $ compute (DV.fromList s) (DV.fromList l)) (scrambleBaseCheck s l)
  where
    compute s l
      | DV.length s <= 3 = return True
      | otherwise = do
        sMap <- HT.new
        flMap <- HT.new
        blMap <- HT.new
        let n = DV.length s

        evalCC $ \ret -> do
          forM_ [0..n - 2] $ \lIdx -> do  -- latest match index
            incMap sMap (DV.unsafeIndex s lIdx)
            incMap flMap (DV.unsafeIndex l lIdx)
            incMap blMap (DV.unsafeIndex l (n - 1 - lIdx))

            whenM (cmpMap sMap flMap) $
              whenM (liftST $ andM
                [ compute
                    (DV.take (lIdx + 1) s)
                    (DV.take (lIdx + 1) l)
                , compute
                    (DV.drop (lIdx + 1) s)
                    (DV.drop (lIdx + 1) l)
                ]) $ ret True

            whenM (cmpMap sMap blMap) $
              whenM (liftST $ andM
                [ compute
                    (DV.take (lIdx + 1) s)
                    (DV.drop (n - lIdx - 1) l)
                , compute
                    (DV.drop (lIdx + 1) s)
                    (DV.take (n - lIdx - 1) l)
                ]) $ ret True

          return False

newtype ScamblePair = ScramblePair (String, String)
  deriving Show


instance Arbitrary ScamblePair where
  arbitrary = do
    (len :: Int) <- abs <$> arbitrary
    l1 <- mapM (const arbLower) [1..len]
    l2 <- shuffle l1
    return $ ScramblePair (l1, l2)
    where
      arbLower = do
        (n :: Int) <- abs <$> arbitrary
        return $ toEnum $ fromEnum 'a' + (n `mod` 26)

-- prop> withMaxSuccess 100000 testIsScrambleString
-- +++ OK, passed 100000 tests.
testIsScrambleString :: ScamblePair -> Bool
testIsScrambleString (ScramblePair (s, l))
  | ls >= 30  = True
  | ls >= 8   = dynamic () == frequency ()
  | ls == 0   = True
  | otherwise =
    let f = frequency () in
    f  == dynamic () && correct () == f
  where ls = length s
        correct () = ShortStuff.correctIsScrambleString s l
        dynamic () = isScrambleString_dynamic s l
        frequency () = isScrambleString_frequency s l


--------------------------------- Minimum Palindrome Cut ---------------------------------

-- | Returns the whole computed `dp` value, each position for the minimum cut until this position
--   Final result should be just the last element of the return list
-- 
-- >>> minPalindromeCut "aab"
-- [0,0,1]
minPalindromeCut :: (Eq a, DVU.Unbox a) => [a] -> [Int]
minPalindromeCut l = runST $ do
  dp <- DVM.generate n id

  forM_ [1..2*n-2] $ \ctr -> do
    -- DEBUG: SHOULD CONSIDER FROM THE CENTER
    -- let left = (ctr - 1) `div` 2
    --     right = left + 1
    let left = ctr `div` 2
        -- so that left = right when ctr is pointing at a real position
        -- that is, this center is considered during the loop
        right = ctr - left
    {- Loop Invariant: the part on left of the center are always correct. -}
    loop dp left right

  DV.toList <$> DV.unsafeFreeze dp
  where
    lst = DVU.fromList l
    n = DVU.length lst
    loop :: DVM.MVector s Int -> Int -> Int -> ST s ()
    loop dp left right
      | left >= 0 && right < n && lst DVU.! left == lst DVU.! right = do
        if left == 0 then DVM.write dp right 0
        else do
          lv <- DVM.read dp $ left - 1
          DVM.modify dp (min $ lv + 1) right
          loop dp (left - 1) (right + 1)
      | otherwise = return ()




-- | Returns the whole computed `dp` value, each position for the minimum cut until this position
--   Final result should be just the last element of the return list
minPalindromeCut_correct :: (Eq a, DVU.Unbox a) => [a] -> [Int]
minPalindromeCut_correct l = runST $ do
  dp <- DVM.generate (n + 1) (\x -> x-1)

  forM_ [1..2*n-2] $ \ctr -> do
    let left = ctr `div` 2
        right = ctr - left
    loop dp left right

  tail . DV.toList <$> DV.unsafeFreeze dp
  where
    lst = DVU.fromList l
    n = DVU.length lst
    loop :: DVM.MVector s Int -> Int -> Int -> ST s ()
    loop dp left right
      | left >= 0 && right < n && lst DVU.! left == lst DVU.! right = do
        lv <- DVM.read dp left
        rv <- DVM.read dp (right + 1)
        DVM.write dp (right + 1) (min rv (lv + 1))
        loop dp (left - 1) (right + 1)
      | otherwise = return ()

-- prop> withMaxSuccess 1000000 testMinPalindromeCut
-- +++ OK, passed 1000000 tests.
testMinPalindromeCut :: String -> Bool
testMinPalindromeCut (str :: String) =
  minPalindromeCut str == minPalindromeCut_correct str


cpsFact :: Num r => r -> r
cpsFact n = evalCont $ cpsFact n
  where
    cpsFact n = do
      v <- cpsFact (n - 1)
      return $ n * v



------------------------------------------ Candy ------------------------------------------

data CandyBag = CandyBag
  { cbPrevVal :: Int
  , cbPrevCandy :: Int
  , cbLeftMostCandy :: Int
  , cbDecWidth :: Int
  , cbCandies :: Int }

-- >>> candy [1,3,2,2,1]
-- 7
candy :: [Int] -> Int
candy lst = case lst of
  []    -> 0
  h:lst -> extract $ foldl compute (newBag h) lst
  where
    newBag h = CandyBag h 1 1 0 1
    extract = cbCandies
    compute bag thisVal
      | cbPrevVal bag < thisVal =
        let thisCandy = cbPrevCandy bag + 1 in
        bag {
          cbPrevVal = thisVal
        , cbPrevCandy = thisCandy
        , cbLeftMostCandy = thisCandy
        , cbDecWidth = 0
        , cbCandies = cbCandies bag + thisCandy
        }
      | cbPrevVal bag == thisVal =
        bag {
          cbPrevVal = thisVal
        , cbPrevCandy = 1
        , cbLeftMostCandy = 1
        , cbDecWidth = 0
        , cbCandies = cbCandies bag + 1
        }
      -- pVal > thisVal
      | cbLeftMostCandy bag > cbDecWidth bag + 1 =
        bag {
          cbPrevVal = thisVal
        , cbPrevCandy = 1
        , cbDecWidth = cbDecWidth bag + 1
        , cbCandies = cbCandies bag + cbDecWidth bag + 1
        }
      | otherwise =
        bag {
          cbPrevVal = thisVal
        , cbPrevCandy = 1
        , cbDecWidth = cbDecWidth bag + 1
        , cbLeftMostCandy = cbDecWidth bag + 2
        , cbCandies = cbCandies bag + cbDecWidth bag + 2
        }

-- >>> candy' [0,1,0,1]
-- 6
candy' :: [Int] -> Int
candy' ratings = case ratings of
  []  -> 0
  lst ->
    scanl1 scanner (zip (repeat 1) lst)
    |> reverse
    |> scanl1 scanner
    |> fmap fst
    |> sum
  where
    scanner (pC, pV) (tC, tV)
      | pV < tV && tC <= pC = (pC + 1, tV)
      | otherwise = (tC, tV)

-- prop> withMaxSuccess 10000000 testCandy
-- +++ OK, passed 10000000 tests.
testCandy :: [Int] -> Bool
testCandy l =
  candy l == candy' l


--------------------------------------- Column Sum ---------------------------------------

-- | Returns the maximum sum of a column of numbers that
--   If a given number of threshold is specified, less than or equal to that
--   Otherwise, simply returns the maximum sum
-- 
-- >>> maxColumnSum [1, 0, 3, -9, 5, 7] Nothing
-- Just 12
-- >>> maxColumnSum [1, 0, 3, -9, 5, 7] $ Just 10
-- Just 7
maxColumnSum :: (Ord b, Num b, Foldable t) => t b -> Maybe b -> Maybe b
maxColumnSum lst bound =
  -- DEBUG: should add [0] as the initial value to cope with the case
  --        when the whole segment is to take -- intuitively, the initial empty prefix is of sum `0`
  flip execState Nothing $ foldM compute (IS.fromList [0], 0) lst
  where
    compute (set, sum) e = do
      let sum' = sum + e
          tree' = IS.insert sum' set
          val = case bound of
            Nothing    -> IS.lookupMin set
            Just bound -> leastUpperBound set (sum' - bound)
      modify' (add $ (sum'-) <$> val)
      return (tree', sum')
    add val ori = liftA2 max val ori <|> val <|> ori
    leastUpperBound set x =
      let (_, b, s) = IS.splitMember x set in
      if b then Just x else IS.lookupMin s

-- | Returns the maximum sum of a sub-matrix within the given matrix no larger than the threshold
-- >>> maxMatrixSum [[1,0,1],[0,-2,3]] $ Just 2
-- Just 2
maxMatrixSum :: (Ord a, Num a) => [[a]] -> Maybe a -> Maybe a
maxMatrixSum matrix bound
  | not $ isMatrix matrix = Nothing
  | null matrix = Nothing
  | null $ head matrix = Nothing
  | otherwise = flip execState Nothing $ do
    matrix <- return $ toVecMat matrix
    let colLen = DV.length $ DV.head matrix
    forM_ [0..colLen-1] $ \left ->
      forM_ [left..colLen-1] $ \right -> do
        let col = flip fmap matrix $ DV.sum . DV.slice left (right - left + 1)
            sum = maxColumnSum col bound
        modify' $ \ori -> liftA2 max sum ori <|> sum <|> ori
  where toVecMat matrix = DV.fromList $ fmap DV.fromList matrix

-- A cooler version -- to use CPS
-- >>> maxMatrixSum' [[1,0,1],[0,-2,3]] $ Just 2
-- Just 2
maxMatrixSum' :: (Ord a, Num a) => [[a]] -> Maybe a -> Maybe a
maxMatrixSum' matrix bound
  | not $ isMatrix matrix = Nothing
  | null matrix = Nothing
  | null $ head matrix = Nothing
  | otherwise = evalCont $ do
    matrix <- return $ toVecMat matrix
    let colLen = DV.length $ DV.head matrix
    forM_ [0..colLen-1] $ \left ->
      forM_ [left..colLen-1] $ \right -> do
        let col = flip fmap matrix $ DV.sum . DV.slice left (right - left + 1)
            sum = maxColumnSum col bound
        shift $ \rest -> do
          let ori = rest ()
          -- Or: ori <- return $ rest ()
          -- Or: if use `shiftT` then ori <- lift $ rest ()
          return $ liftA2 max sum ori <|> sum <|> ori
    return Nothing
  where toVecMat matrix = DV.fromList $ fmap DV.fromList matrix


------------------------------------- N Stock -------------------------------------

-- | Complexity O(nm) `n` is the given times of maximum transactions
--   while `m` is the length of `prices`
-- 
-- >>> nStock [3,3,5,0,0,3,1,4] 2
-- 6
-- >>> nStock [1,2,3,4,5] 2
-- 4
-- >>> nStock [7,6,4,3,1] 2
-- 0
-- >>> nStock [3,3,5,0,0,3,1,4] 10
-- 8
nStock :: (Num a, Num p, Enum a, Ord a, Ord p) => [p] -> a -> p
nStock prices n
  | n <= 0 = 0
  | otherwise = case prices of
    []   -> 0
    p:ps -> 
      -- one more at the end, to keep every functional ones updated
      -- as `scanr1` will never touch the ending element
      let lst = [0..n] $> (-p,0) in
      snd $ head $ foldl (flip $ scanr1 . scanner) lst ps
  -- DEBUG: In `scanr1`, the previous determined element is ON-THE-RIGHT
  where scanner p (b, s) (_, ps) = let b' = max b (ps - p) in (b', max s (b' + p))



--------------------------------------- BFS Shortest Path ---------------------------------------



bfsShortestPath :: (Hashable t2, Eq t2) => t2 -> t2 -> (t2 -> [t2]) -> [[t2]]
bfsShortestPath src tar getNext = runST $ do
  let q = Seq.empty Seq.|> src
  visited <- HT.new
  pred <- HT.new
  HT.insert visited src (0 :: Int)
  loop pred visited q getNext
  dfsPaths pred src tar
  where
    -- dfsPaths :: (Hashable t2, Eq t2) => HT.HashTable s t2 [t2] -> t2 -> t2 -> ST s [[t2]]
    dfsPaths pred src node
      | node == src = return [[src]]
      | otherwise   = do
        val <- fromMaybe [] <$> HT.lookup pred node
        L.observeAllT $ do
          n <- toLogicT val
          val <- toLogicT =<< liftST (dfsPaths pred src n)
          return $ node:val
    -- loop :: (Hashable t2, Eq t2) => HT.HashTable s t2 [t2]
    --   -> HT.HashTable s t2 Int -> Seq.Seq t2 -> (t2 -> [t2]) -> ST s ()
    loop pred visited q getNext = case Seq.viewl q of
      Seq.EmptyL   -> return ()
      node Seq.:< q' -> do
        lv <- fromJust <$> HT.lookup visited node
        q' <- foldM (folder (node, lv) pred visited) q' (getNext node)
        loop pred visited q' getNext
    folder (pNode, pLv) pred visited q node =
      HT.lookup visited node >>= \case
        Just lv | lv == pLv + 1 -> do addToPred pred node pNode; return q
        Just _  -> return q
        Nothing -> do HT.insert visited node (pLv + 1); return $ q Seq.|> node
    addToPred pred node pNode = do
      HT.mutate pred node $ \case
        Nothing  -> (Just [pNode], ())
        Just lst -> (Just (pNode:lst), ())

