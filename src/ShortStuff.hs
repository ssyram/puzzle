{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}
module ShortStuff where

import Debug.Trace
import Data.Maybe
import Utils
import MyData.Vector
import Data.List as List
import Control.Monad.State.Strict
import Data.Array
import Control.Monad.ST
import qualified Data.Array.Base
import Data.Array.ST
import Data.STRef
import Test.QuickCheck
import qualified Data.Set as Set
import Data.Hashable
import Data.Bits
import Data.HashTable.Class hiding (foldM)
import qualified Data.HashTable.ST.Basic as HashTable
import Numeric
import Data.Char
import WorkingTest (lst)
import Data.Ratio
import Test.QuickCheck.Poly (C(unC))
import Control.Arrow (Arrow(arr))
import GHC.Generics
import Text.Read (Lexeme(String))
import qualified Control.Monad.ST.Trans as STT
import Data.Array.Base (listArrayST)
import Data.Foldable (foldrM)
import qualified Data.Array.MArray as STT
import Control.Applicative

-- This file is about short stuff for one or just a few functions / supporting data type

-- =============== Median: Add Two Numbers ====================
-- https://leetcode.com/problems/add-two-numbers/

{- | A list that just contains [0 - 9] for each position

For example, NumberList [2, 3, 4] represents number 234

Speicial Note: NumberList with 0 in its head and it is not 0 is illed form
-}
newtype NumberList = NumberList [Int] deriving (Show)

-- The function to format the given list -- return a non-illed form of the list
formatNumberList (NumberList _) = undefined

matchLength :: (Num a1, Num a2) => [a2] -> [a1] -> ([a2], [a1])
matchLength l1 l2 =
  let lengthDiff = length l1 - length l2 in
  if lengthDiff > 0 then (l1, replicate lengthDiff 0 ++ l2)
  else (replicate lengthDiff 0 ++ l1, l2)

addNumberList :: NumberList -> NumberList -> NumberList
addNumberList (NumberList l1) (NumberList l2) =
  let (l1', l2') = matchLength l1 l2 in
  -- trace (show l1' ++ "; " ++ show l2') $ NumberList []
  let (res, addPos) = add l1' l2' in
  NumberList $ if addPos > 0 then addPos:res else res
  where
    addSinglePos x y =
      if x + y >= 10 then (x + y - 10, 1)
      else (x + y, 0)
    -- add [x] [y] = let (num, addPos) = addSinglePos x y in ([num], addPos)
    add []  []  = ([], 0)
    add (x:l1') (y:l2') =
      let (res, addPos) = add l1' l2' in
      let (posNum, newAddPos) = addSinglePos x (y + addPos) in
      (posNum:res, newAddPos)
    add _ _ = undefined

-- A reversed version of number list -- 1234 is represented by [4, 3, 2, 1]
newtype ReverseNumberList = ReverseNumberList [Int] deriving (Show)

matchLengthOfReverseNumberList :: (Num a1, Num a2) => [a2] -> [a1] -> ([a2], [a1])
matchLengthOfReverseNumberList l1 l2 =
  let ld = length l1 - length l2 in
  if ld > 0 then (l1, l2 ++ replicate ld 0)
  else (l1 ++ replicate ld 0, l2)

addReversedNumberList :: ReverseNumberList -> ReverseNumberList -> ReverseNumberList
addReversedNumberList (ReverseNumberList l1) (ReverseNumberList l2) =
  let (l1', l2') = matchLengthOfReverseNumberList l1 l2 in
  ReverseNumberList $ add l1' l2' 0
  where
    add [] [] n = [1 | n > 0]
    add (x:l1) (y:l2) n =
      if x + y + n >= 10 then (x+y+n-10):add l1 l2 1
      else (x+y+n):add l1 l2 0
    add _ _ _ = undefined


-- ================ Hard: Binary Median Search in Two Sorted Arrays ===========================
-- Given two sorted arrays, find the median of the merged array, but in log(m + n)

{-| The idea behind is simple: use binary search simultaneously in all two arrays

until the sum of the two array position reached half of the sum of their lengths
-}
-- findMedianInTwoSortedArrays :: Array Int Int -> Array Int Int -> Rational
-- findMedianInTwoSortedArrays a1 a2 =
--   let curPointer = (a1, m `div` 2) in
--   let ~(res, pointerA1, pointerA2) =
--         iter ((m + n) `div` 2) curPointer (Just $ m `div` 2) (findPlace a2 $ fromJust $ at a1 $ m `div` 2) in
--   if odd $ (m + n) `div` 2 then res
--   else
--     let x = case at a1 (pointerA1 + 1) of
--               Just x ->
--                 case at a2 (pointerA2 + 1) of
--                   Just x' -> if x > x' then x' else x
--                   Nothing -> x
--               Nothing -> fromJust $ at a2 (pointerA2 + 1)
--     in
--     (res + toRational x) / 2
--   where
--     m = let (max, min) = bounds a1 in max - min
--     n = let (max, min) = bounds a2 in max - min
--     findPlace a n = undefined
--     iter target = undefined
--     at :: (Num i, Ix i) => Array i e -> i -> e
--     at a pos =
--       let (max, min) = bounds a in a!(min + pos)
--       -- if min + pos > max then Nothing else Just $ a!(min + pos)

standardToArray :: [e] -> Array Int e
standardToArray lst = listArray (0, length lst - 1) lst

mergeSortedList :: Ord a => [a] -> [a] -> [a]
mergeSortedList (s:l1) (s':l2)
  | s > s' = s':mergeSortedList (s:l1) l2
  | otherwise = s:mergeSortedList l1 (s':l2)
mergeSortedList [] l2 = l2
mergeSortedList l1 [] = l1

standardFindMedianInTwoSortedArrays :: Array Int Int -> Array Int Int -> Rational
standardFindMedianInTwoSortedArrays a1 a2 =
  let lst = mergeSortedList (Data.Array.elems a1) (Data.Array.elems a2) in
  trace (show lst) $
  median $ listArray (0, length lst - 1) lst

at :: (Ix i, Num i) => Array i e -> i -> e
at a pos = let (min, _) = bounds a in a!(min + pos)

median :: (Integral a, Ix a, Real e) => Array a e -> Rational
median a =
  let (lb, ub) = bounds a in
  if even $ ub - lb + 1 then toRational (at a ((ub - lb + 1) `div` 2) + at a ((ub - lb + 1) `div` 2 - 1)) / 2
  else toRational (at a ((ub - lb + 1) `div` 2))

findMedianInTwoSortedArrays :: Array Int Int -> Array Int Int -> Rational
findMedianInTwoSortedArrays a1 a2
  | len a1 == 0 && len a2 == 0 = error "Invalid Input"
  | len a1 == 0 = median a2
  | len a2 == 0 = median a1
  | otherwise = findMedian a1 a2 (bounds a1) (bounds a2)
  where
    len a = let (lb, ub) = bounds a in ub - lb
    findMedian :: Array Int Int -> Array Int Int -> (Int, Int) -> (Int, Int) -> Rational
    findMedian a1 a2 (lb1, ub1) (lb2, ub2) =
      let a1Mid = (ub1 - lb1) `div` 2 + lb1 in
      let a2Pos = findPlace a2 (lb2, ub2) a1Mid in
      let sum = a1Mid + a2Pos in
      let tar = (len a1 + len a2) `div` 2 in
      if sum > tar then findMedian a2 a1 (lb2, a2Pos) (lb1, ub1)
      else if sum < tar then findMedian a2 a1 (a2Pos, ub2) (lb1, ub1)
      -- else ((a1, a1Mid), (a2, a2Pos))
      else
        let curRes = at a1 a1Mid in
        if even $ len a1 + len a2 then
          let another =
                let backA1 = at a1 $ a1Mid - 1 in
                let backA2 = at a2 $ a2Pos - 1 in
                if a1Mid == 0 then backA2
                else if a2Pos == 0 then backA1
                else min backA1 backA2
          in
          toRational (curRes + another) / 2
        else toRational curRes
      where
        findPlace a (lb, ub) tar
          | ub == lb = at a lb
          | ub < lb = error "Invalid Input: ub < lb"
          | otherwise =
              let cur = (ub - lb) `div` 2 + lb in
              let curVal = at a cur in
              if curVal < tar then findPlace a (cur, ub) tar
              else if curVal > tar then findPlace a (lb, cur) tar
              else cur


-- =================== Longest Palindrome O(n) =================

data LongestPalindromeResult a n =
    LongestPalindromeResult
    { mode :: String,
      rest :: [a],
      former :: [a],
      lowerBound :: n,
      curNode :: n,
      internalBound :: n,
      result :: [n] }

simplerLongestPalindrome :: (Eq a, Show a) => [a] -> (Int, [a])
simplerLongestPalindrome str =
  if null str then (0, []) else
  trace ("Length of AppendedStr: " ++ show (length appendedStr)) $
  decorateResult $ foldl foldFunc (initRes appendedStr) $ zip [0..] appendedStr
  where
    appendedStr = tail $ do { c <- str; [Nothing, Just c] }
    decorateResult res =
      let (maxId, maxRadius) =
            foldl1
            (\x y ->
              if snd x > snd y then x
              else if (snd y > snd x) || ((snd x == snd y) && isNothing (appendedStr !! fst x)) then y
              else x) $
            zip [0..] $ reverse $ result res
      in
      trace ("Here" ++ show (reverse $ result res)) $
      let rs = do { c <- slice (maxId - maxRadius) (maxId + maxRadius) appendedStr; maybe [] return c } in
      (length rs, rs)
    initRes str =
      LongestPalindromeResult {
        mode = "Search From Start",
        rest = str,
        former = [],
        lowerBound = 0,
        curNode = 0,
        internalBound = 0,
        result = []
      }
    foldFunc curRes newC
      | mode curRes == "Search From Start" =
        trace ("Start Seaching From Start, with: " ++ show newC) $
        let lengthForCurrentNode =
              getLongestPalindrome (drop (lowerBound curRes) (latter curRes))
                                   (drop (lowerBound curRes) (former curRes)) (lowerBound curRes) in
        let nextRes = addNewLength lengthForCurrentNode curRes in
        startSearchInternal nextRes
      | mode curRes == "Internal Search" =
        trace ("Start Seaching From Internal, with: " ++ show newC) $
        if curNode curRes > internalBound curRes then
          {- 
            BUG DETECTED: if ending this time of loop here, the pointer will move to the next place rather in the head of "rest res"
            bias will enlarge when time goes
          -}
          searchFromStart curRes else
        let !dtb = distanceToBound curRes in
        let !mr = mirrorRadius curRes in
        if mr > dtb then
          trace "mr > dtb" $
          let nextRes = addNewLength dtb curRes in searchNextInternal nextRes
        else if mr < dtb then
          trace "mr < dtb" $
          let nextRes = addNewLength mr curRes in searchNextInternal nextRes
        else
      {-
      BUG DETECTED: each time to end the loop here, the next loop will start rather than the current node, the bias will enlarge
      -}   startSeachingFromStartWithLowerBound mr curRes
      | otherwise = error "No Such Mode"
      where
        getLongestPalindrome :: (Eq a, Integral n) => [a] -> [a] -> n -> n
        getLongestPalindrome (x:xs) (y:ys) n = if x == y then getLongestPalindrome xs ys (n + 1) else n
        getLongestPalindrome []     _      n = n
        getLongestPalindrome _      []     n = n
        addNewLength n res =
          trace ("Call add length. Current result: " ++ show (result res) ++ "; with new append: " ++ show n) $
          res { result = n:result res }
        latter = tail . rest
        startSearchInternal res = res {
          mode = "Internal Search",
          curNode = 1,
          internalBound = case result res of { s:_ -> s; _ -> error "Impossible" },
          rest = tail $ rest res,
          former = head (rest res):former res
        }
        searchFromStart res = res { mode = "Search From Start", lowerBound = 0 }
        distanceToBound res = internalBound res - curNode res
        mirrorRadius res =
          trace ("In Mirror Radius" ++ show (result res) ++ show (curNode res) ++ "; bound = " ++ show (internalBound res)) $
          result res !! (2 * curNode res - 1)
        searchNextInternal res = res {
          curNode = curNode res + 1,
          rest = tail $ rest res,
          former = head (rest res):former res
        }
        startSeachingFromStartWithLowerBound lb res =
          trace ("Current Lower Bound = " ++ show (lowerBound res) ++ "; To update to: " ++ show lb) $
          res {
            mode = "Search From Start",
            lowerBound = lb
          }


longestPalindrome :: (Eq a, Show a) => [a] -> (Int, [a])
longestPalindrome str =
  if null str then (0, []) else
  let infoOfAppendedStr = compute [] appendedStr [] 0 in
  trace (show appendedStr) $
  getResultFrom infoOfAppendedStr
  where
    -- "abc" -> tail "|a|b|c" -> "a|b|c"
    appendedStr = tail $ do { c <- str; [Nothing, Just c] }
    getResultFrom infoOfAppendedStr =
      trace (show infoOfAppendedStr) $
      let (maxId, maxRadius) =
            foldl1
            (\x y ->
              if snd x > snd y then x
              else if (snd y > snd x) || ((snd x == snd y) && isNothing (appendedStr !! fst x)) then y
              else x) $
            zip [0..] infoOfAppendedStr
      in
      let rs = do { c <- slice (maxId - maxRadius) (maxId + maxRadius) appendedStr; maybe [] return c } in
      (length rs, rs)
    getLongestPalindrome :: (Eq a) => [a] -> [a] -> Int -> Int
    getLongestPalindrome (s:str) (s':preStk) n =
      if s == s' then getLongestPalindrome str preStk (n + 1) else n
    getLongestPalindrome _ [] n = n
    getLongestPalindrome [] _ n = n
    -- compute :: (Eq a) => [Int] -> [a] -> [a] -> Int -> [Int]
    compute curInfo str preStk lowerBound =
      case str of
        []   -> reverse curInfo
        _:ss ->
          trace ("DroppedStr = " ++ show (drop lowerBound str) ++ "; DroppedPreStk = " ++ show (drop lowerBound preStk)) $
          let nextRadius = getLongestPalindrome (drop lowerBound ss) (drop lowerBound preStk) lowerBound in
          -- trace ("Next Radius: " ++ show nextRadius) $
          let nextInfo = nextRadius:curInfo in
          computeInternal 1 nextRadius nextInfo str preStk
    -- computeInternal :: (Eq a) => Int -> Int -> [Int] -> [a] -> [a] -> [Int]
    computeInternal cur bound info str preStk =
      trace ("Cur = " ++ show cur ++ "; Bound = " ++ show bound ++ "; Info = " ++ show info ++ "; str = " ++ show str ++
      "; preStk = " ++ show preStk) $
      if cur > bound then
        trace "Cur > Bound" $
        let (str', preStk') = passOnTo str preStk (bound + 1) in compute info str' preStk' 0
      else
        let mirrorRadius = info !! (2 * cur - 1) in
        let distanceToBound = bound - cur in
        if mirrorRadius > distanceToBound then
          trace ("Trigger > " ++ show (distanceToBound:info)) $
          computeInternal (cur + 1) bound (distanceToBound:info) str preStk
        else if mirrorRadius < distanceToBound then
          trace "Trigger < " $
          computeInternal (cur + 1) bound (mirrorRadius:info) str preStk
        else
          trace ("Trigger == " ++ show cur) $
          let (str', preStk') = passOnTo str preStk cur in
          trace ("str' = " ++ show str' ++ "; preStk' = " ++ show preStk') $
          compute info str' preStk' distanceToBound
      where
        passOnTo :: [a] -> [a] -> Int -> ([a], [a])
        passOnTo str stk bound =
          if bound <= 0 then (str, stk)
          else case str of { s:str' -> passOnTo str' (s:stk) (bound - 1); [] -> error "Impossible" }

-- toPrint =
--   putStrLn $ do
--   c <- ['A' .. 'Z']
--   "\\def\\script" ++ [c] ++ "{\\mathcal{" ++ [c] ++ "}}\n"

-- ========================== Easy: find two numbers ===============================

-- | >>> findTwoIndices [2,7,11,15] 9
-- [(1,0)]
findTwoIndices :: (Enum b, Ord b, Num b, Num a, Eq a) => [a] -> a -> [(b, b)]
findTwoIndices lst target = [(i, j) | (i, x) <- zip [0..] lst, (j, y) <- zip [0..] lst, i > j, x + y == target]


-- ========================= Medium: easy find palindrome ===========================

{-| longest palindrome

>>> easyFindLongestPalindrome ""
(0,"")
-}
easyFindLongestPalindrome :: Eq a => [a] -> (Int, [a])
easyFindLongestPalindrome s =
  if null s then (0, []) else
  let insertedS = tail $ do { c <- s; [Nothing, Just c] } in
  getResult $
  fromJust $
  foldl foldFunc Nothing [(reverse $ take n insertedS, drop n insertedS) | n <- [0..length insertedS - 1]]
  where
    getResult (n, ~(x:xs)) =
      let lst = take n xs in
      let res = [tx | x <- reverse lst ++ [x] ++ lst, isJust x, let Just tx = x] in
      (length res, res)
    foldFunc Nothing (_, lst) = return (0, lst)
    foldFunc tmpRes@(Just (oldRadius, _)) (preStk, ~lst@(_:xs)) =
      let radius = findRadius preStk xs in
      let trueRadius = if radius > 0 && isNothing (preStk !! (radius - 1)) then radius - 1 else radius in
      if oldRadius < trueRadius then return (trueRadius, lst) else tmpRes
      where
        findRadius stk tl =
          tfr stk tl 0
          where
            tfr [] _ n = n
            tfr _ [] n = n
            tfr (x:xs) (y:ys) n = if x == y then tfr xs ys $ n + 1 else n


-- ========================= 3 Sum ===============================

-- | Given a list of numbers, divide them into triples that sum up to 0

-- >>> simpleTripets [-1,0,1,2,-1,-4]
-- [(-1,-1,2),(-1,0,1)]
threeSum :: (Num c, Ord c) => [c] -> [(c, c, c)]
threeSum lst =
  unique
  [(a', b', c') |
   (i, a) <- zip [0 .. ] lst,
   (j, b) <- zip [0 .. ] lst,
   i > j,
   (k, c) <- zip [0 .. ] lst,
   j > k,
   a + b + c == 0,
   let [a', b', c'] = sort [a, b, c]]
   where
     unique :: (Ord n) => [n] -> [n]
     unique lst =
       uq $ sort lst
       where
         uq :: (Eq a) => [a] -> [a]
         uq (x:y:xs) = (if x == y then uq else (x:) . uq) (y:xs)
         uq lst      = lst

-- ====================== Closest 3 Sum ==========================

-- >>> closestThreeSum [0, 0, 0] 1
-- Just (0,1,2,0)
closestThreeSum :: (Num c, Enum c, Ord a, Ord c, Num a) => [a] -> a -> Maybe (c, c, c, a)
closestThreeSum lst target =
  case lst of
    -- if length is at least 3
    _:_:_:_ ->
      return $
      minimumBy (\(_, _, _, s1) (_, _, _, s2) -> compare (abs $ s1 - target) (abs $ s2 - target))
      [(i, j, k, sum) |
      (i, a) <- zip [0 .. ] lst,
      (j, b) <- zip [0 .. ] lst,
      i < j,
      (k, c) <- zip [0 .. ] lst,
      j < k,
      let sum = a + b + c]
    _ -> Nothing

testState :: State Int ()
testState =
  do
    plus1
    plus1
  where
    plus1 = do { n <- get; put $ n + 1}

-- >>> testRunState
-- 3
testRunState = execState testState 1

-- ====================== Medium: generate parentheses ======================

{-| Key idea: use Dyck language "D := () | (D)D" -}

-- >>> generateParentheses 3
-- ["((()))","(()())","(())()","()(())","()()()"]
generateParentheses :: Integer -> [String]
generateParentheses n =
  if n <= 0 then [""] else
  gp 1 [["()"], [""]] [[""], ["()"]]
  where
    -- k is the length of lst
    gp :: Integer -> [[String]] -> [[String]] -> [String]
    gp k lst revLst =
      if k >= n then head lst else
      let next :: [String] = do {
        -- xs and ys combines have the same size
        (xs, ys) <- zip lst revLst;
        ["(" ++ x ++ ")" ++ y | x <- xs, y <- ys]
      }
      in
      gp (k + 1) (next : lst) (revLst ++ [next])

-- ===================== Medium: Phone Letter Combination ========================

-- simplePrinter :: String
-- simplePrinter = do
--   num <- [2..9]
--   "dictionary '" ++ show num ++ "' = \"" ++ take 3 (drop (3 * (num - 2)) ['a'..'z']) ++ "\"\n"

-- >>> phoneLetterCombination "2"
-- ["a","b","c"]
-- >>> phoneLetterCombination "23"
-- ["ad","ae","af","bd","be","bf","cd","ce","cf"]
phoneLetterCombination :: String -> [String]
phoneLetterCombination str =
  -- case str of
  --   [] -> []
  --   [x] -> (:[]) <$> dictionary x
  --   x:str -> do
  --     head <- dictionary x
  --     rest <- phoneLetterCombination str
  --     return $ head : rest
  if null str then [] else
  foldr ((<*>) . fmap (:)) [""] $ fmap dictionary str
  where
    dictionary '2' = "abc"
    dictionary '3' = "def"
    dictionary '4' = "ghi"
    dictionary '5' = "jkl"
    dictionary '6' = "mno"
    dictionary '7' = "pqrs"
    dictionary '8' = "tuv"
    dictionary '9' = "wxyz"
    dictionary _   = error "Undefined"


-- ========================== Medium: Swap nodes in pairs ====================

swapNodesInPairs :: [a] -> [a]
swapNodesInPairs lst =
  case lst of
    [] -> []
    [a] -> [a]
    a:b:lst -> b:a:swapNodesInPairs lst


-- ======================== Hard: Longest Valid Parentheses ==================

{-| Standard anwser to longest valid parentheses

The idea is to traverse forward and backward in order to get rid of the effect cause by internal "(".
This is the same as what I have conceived, but the key then left is how to cope with consequent ones like "()()"
Here, the technique to cope with it is that it records the current length but not clear the stack
    and keep left and right at the same time rather than just one stack -- one stack cannot distinguish 
    different cases.

>>> correctLongestValidParentheses "(()((()("
2
>>> correctLongestValidParentheses "(()()("
4
-}
correctLongestValidParentheses :: String -> Int
correctLongestValidParentheses str =
  (\(_, _, _, maxLen) -> maxLen) $
  ($ init) $
  execState $ do
    prepareScanFromLeft
    cfor (not . null . getStr) nextStr $ do
      c <- getNextChar
      left <- getLeft
      right <- getRight
      if c == '(' then putLeft $ left + 1
      else if c == ')' then putRight $ right + 1
      else error $ "Invalid Char '" ++ [c] ++ "'"
      left <- getLeft
      right <- getRight
      when (left == right) $ do
        maxLen <- getMaxLen
        putMaxLen $ max maxLen (left + right)
      when (right > left) $ do
        putLeft 0
        putRight 0
    prepareScanFromRight
    cfor (not . null . getStr) nextStr $ do
      c <- getNextChar
      left <- getLeft
      right <- getRight
      if c == '(' then putLeft $ left + 1
      else if c == ')' then putRight $ right + 1
      else error $ "Invalid Char '" ++ [c] ++ "'"
      left <- getLeft
      right <- getRight
      when (left == right) $ do
        maxLen <- getMaxLen
        putMaxLen $ max maxLen (left + right)
      when (left > right) $ do
        putLeft 0
        putRight 0
  where
    nextStr = modify $ \(~(_:str), left, right, maxLen) -> (str, left, right, maxLen)
    -- | (str, left, right, maxLen)
    init = ("", 0, 0, 0)
    prepareScanFromLeft = modify $ \(_, _, _, c) -> (str, 0, 0, c)
    prepareScanFromRight = modify $ \(_, _, _, c) -> (reverse str, 0, 0, c)
    getStr (str, _, _, _) = str
    getNextChar = do { (~(h:_), _, _, _) <- get; return h }
    getLeft = do { (_, left, _, _) <- get; return left }
    getRight = do { (_, _, right, _) <- get; return right }
    putLeft newLeft = modify $ \(str, _, right, maxLen) -> (str, newLeft, right, maxLen)
    putRight newRight = modify $ \(str, left, _, maxLen) -> (str, left, newRight, maxLen)
    getMaxLen = do { (_, _, _, maxLen) <- get; return maxLen }
    putMaxLen newMaxLen = modify $ \(str, left, right, _) -> (str, left, right, newMaxLen)


-- =============================== k Group Reverse ===================================

{-| easy version of k reverse

>>> kGroupReverse [1,2,3,4,5] 1
[1,2,3,4,5]
>>> kGroupReverse [1,2,3,4,5] 2
[2,1,4,3,5]
>>> kGroupReverse [1,2,3,4,5] 3
[3,2,1,4,5]
>>> kGroupReverse [1,2,3,4,5,6] 3
[3,2,1,6,5,4]
>>> kGroupReverse [1] 2
[1]
-}
kGroupReverse :: [a] -> Int -> [a]
kGroupReverse lst k =
  -- first a guarded definition
  if k <= 0 then [] else kGroupReverse lst k
  where
    kGroupReverse lst k =
      let (hd, rst) = splitAt k lst in
      if null rst then if length hd /= k then hd else reverse hd
      else reverse hd ++ kGroupReverse rst k

-- ===================================== First Missing Positive ======================================

{-| A time in O(n log n), space in O(1) version -}
correctFirstMissingPositive :: (Num a, Ord a) => [a] -> a
correctFirstMissingPositive lst =
  foldl (\res n -> if res == n then res + 1 else res) 1 $ sort lst

{-| Key idea to a quicker solution: let the number to get to its own index place if possible, so every hole is then fitted 
Finally, let find the acutal number by just traversing the whole modified string again to detect holes
But this is not friendly to Haskell.

Another key obeservations: this missing positive number must happen in 1..length lst.

Since Haskell does not allow leaking of the array back into the environment, it is impossible to implement one
so, here, we implement the idea behind but will require creating a mutable array inside a function

prop> withMaxSuccess 100000 $ \(l :: [Int]) -> correctFirstMissingPositive l == quickFirstMissingPositive l
+++ OK, passed 100000 tests.
-}
quickFirstMissingPositive :: [Int] -> Int
quickFirstMissingPositive lst =
  runST $ do
    let len = length lst
    arr <- newArray_ (1, len) :: ST s (STArray s Int Int)
    forM_ (zip [1..] lst) $ uncurry (writeArray arr)
    -- =====================================================================
    -- from here on, the result is of space O(1) and is irrelevant to lst ||
    -- =====================================================================
    (min, max) <- Data.Array.ST.getBounds arr
    -- supporting functions
    let readAt pos = readArray arr (pos + min - 1)
    let writeAt pos = writeArray arr (pos + min - 1)
    let len = max - min + 1
    -- !_ <- trace ("length = " ++ show len ++ "; min = " ++ show min ++ "; max = " ++ show max) $ return ()
    -- remove all possible obstacles
    forM_ [1..len] $ \pos -> do
      val <- readAt pos
      when (val <= 0 || val > len) $ writeAt pos 0
    -- newLst <- forM [1..len] readAt
    -- !_ <- trace ("lst before shifting = " ++ show newLst) $ return ()
    forM_ [1..len] $ \pos -> do
      -- stay and shift locally until OK
      whileM (do { posVal <- readAt pos; return $ posVal /= 0 && posVal /= pos}) $ do
        posVal <- readAt pos
        let tarPos = posVal
        tarVal <- readAt tarPos
        if tarVal /= tarPos then do
          -- conduct shifting
          writeAt tarPos posVal
          writeAt pos tarVal
        else
          -- duplicate value, just erase
          writeAt pos 0
    -- newLst <- forM [1..len] readAt
    -- !_ <- trace ("result lst = " ++ show newLst) $ return ()
    foldl (\v pos -> do v <- v; nv <- readAt pos; if v == nv then return $ v + 1 else return v) (return 1) [1..len]


-- ================================ Solve Sudoku ============================

-- >>> isValidSudokuBoard (map (map (:[])) $ solveSudoku board)
-- True
-- >>> isValidSudokuBoard board
-- True
isValidSudokuBoard :: [[String]] -> Bool
isValidSudokuBoard board =
  checkShapeValidity board &&
  -- trace "Shape test passed" 
  checkLinesValidity board &&
  -- trace "Line test passed"
  checkColumnsValidity board &&
  -- trace "Column test passed"
  checkLittleMatrixValidity board
  where
    checkShapeValidity board =
      lenEq 9 board && and [lenEq 9 line | line <- board]
    checkLinesValidity :: [[String]] -> Bool
    checkLinesValidity lines =
      and $ do
        fst . foldl
          (\(res, accLines) s ->
            if not res || s == "." then (res, accLines)
            else
              let readResult = readsPrec 1 s :: [(Int, String)] in
              if length readResult /= 1 then (False, accLines)
              else
                let (num, _) = head readResult in
                if num `elem` accLines then (False, accLines)
                else (True, num:accLines)) (True, []) <$> lines
    checkColumnsValidity board =
      checkLinesValidity $ do
        columnNum <- [0..8]
        return [line !! columnNum | line <- board]
    checkLittleMatrixValidity :: [[String]] -> Bool
    checkLittleMatrixValidity board =
      checkLinesValidity $ do
        lCoor <- [0..2]
        cCoor <- [0..2]
        let !lst = do
              line <- take 3 $ drop (lCoor * 3) board
              take 3 $ drop (cCoor * 3) line
        -- !_ <- trace ("matrix value of " ++ show (lCoor + 1, cCoor + 1) ++ " = " ++ show lst) return ()
        return lst

board :: [[String]]
board = [["5","3",".",".","7",".",".",".","."],
         ["6",".",".","1","9","5",".",".","."],
         [".","9","8",".",".",".",".","6","."],
         ["8",".",".",".","6",".",".",".","3"],
         ["4",".",".","8",".","3",".",".","1"],
         ["7",".",".",".","2",".",".",".","6"],
         [".","6",".",".",".",".","2","8","."],
         [".",".",".","4","1","9",".",".","5"],
         [".",".",".",".","8",".",".","7","9"]]

-- printSudokuBoard :: [String] -> String
-- printSudokuBoard board = do
--   (lineNum, line) <- zip [1..] board
--   let (first, left) = splitAt 3 line
--   let (second, third) = splitAt 3 left
--   "||" ++ first ++ '|':second ++ '|':third ++ "||\n"

{-| A function try solving a given Sudoku board

>>> solveSudoku board
===========================
|| 5 3 4 | 6 7 8 | 9 1 2 ||
|| 6 7 2 | 1 9 5 | 3 4 8 ||
|| 1 9 8 | 3 4 2 | 5 6 7 ||
||-------+-------+-------||
|| 8 5 9 | 7 6 1 | 4 2 3 ||
|| 4 2 6 | 8 5 3 | 7 9 1 ||
|| 7 1 3 | 9 2 4 | 8 5 6 ||
||-------+-------+-------||
|| 9 6 1 | 5 3 7 | 2 8 4 ||
|| 2 8 7 | 4 1 9 | 6 3 5 ||
|| 3 4 5 | 2 8 6 | 1 7 9 ||
===========================
-}
solveSudoku :: [[String]] -> [String]
solveSudoku lst =
  runST $ do
    -- Initialise the Sudoku Context
    board <- newArray_ (1, 9) :: ST s (STArray s Int (STArray s Int (Maybe Int)))
    -- answers <- newSTRef [] :: ST s (STRef s [[String]])
    todoMatrix <- forM (zip [1..] lst) $ \(lineNum, lineVal) -> do
      subLine <- newArray_ (1, 9)
      todoLst <- forM (zip [1..] lineVal) $ \(columnNum, valStr) ->
        let [valChar] = valStr in
        if valChar == '.' then do
          writeArray subLine columnNum Nothing
          return $ Just (lineNum, columnNum)
        else do
          writeArray subLine columnNum $ Just $ read [valChar]
          return Nothing
      writeArray board lineNum subLine
      return todoLst
    let todo = [ p | lst <- todoMatrix, x <- lst, isJust x, let Just p = x ]
    -- supporting functions
    let
      at line column = do
        arr <- readArray board line
        readArray arr column
      writeAt line column val = do
        arr <- readArray board line
        writeArray arr column val
      possibleVals pos = do
        possibleLineVals <- getPossibleLineVals pos
        possibleColumnVals <- getPossibleColumnVals pos
        possibleLocalMatrixVals <- getPossibleLocalMatrixVals pos
        return [v | v <- possibleLineVals, v `elem` possibleColumnVals, v `elem` possibleLocalMatrixVals]
        where
          getPossibleLineVals (line, column) = do -- same line different column
            hasLst <- forM [1..9] $ \col -> do
              if col == column then return Nothing
              else at line col
            return [x | x <- [1..9], Just x `notElem` hasLst]
          getPossibleColumnVals (line, column) = do
            hasLst <- forM [1..9] $ \ln -> do
              if ln == line then return Nothing
              else at ln column
            return [x | x <- [1..9], Just x `notElem` hasLst]
          getPossibleLocalMatrixVals (line, column) = do
            let lineBase = ((line - 1) `div` 3) * 3
                columnBase = ((column - 1) `div` 3) * 3
            hasLst <- forM [(x, y) | x <- [1..3], y <- [1..3]] $ \(ln, col) -> do
              let tln = ln + lineBase
                  tcol = col + columnBase
              if line == tln && column == tcol then return Nothing
              else at tln tcol
            return [x | x <- [1..9], Just x `notElem` hasLst]
      findVal todo =
        if null todo then return True else do
        let ~(pos:nextTodo) = todo
        vals <- possibleVals pos
        let (line, column) = pos
        if null vals then return False
        else
          foldM (\res val ->
            if res then return res else do
            writeAt line column $ Just val
            nextRes <- findVal nextTodo
            -- if this value is the true one, return yes, which stops trying other values, otherwise, return false
            -- which continue trying other values
            if nextRes then return True else do
              writeAt line column Nothing
              return False) False vals
    -- do the job here
    res <- findVal todo
    if not res then return ["No Result"]
    else
      -- collect the information and return
      forM [1..9] $ \line ->
        forM [1..9] $ \column -> do
          val <- at line column
          let [c] = show $ fromJust val
          return c

-- =================================== Search Rotated Array ==========================

{-| In order to solve the problem quickly, solve it within the context of ST

prop> withMaxSuccess 1000000 testSearchProperty
+++ OK, passed 1000000 tests.
-}
testSearchProperty :: [Int] -> Int -> Int -> Bool
testSearchProperty (lst :: [Int]) (val :: Int) (rotate :: Int) =
  let rot = if null lst then 0 else abs $ rotate `mod` length lst in
  let l = (`rotateList` rot) $ reverse $ unique lst in
  -- trace ("Property to test: \n\tlst = " ++ show l ++ "\n\tval = " ++ show val) $
  let correctVal = searchLst l val in
  let testVal = pureSearchRotatedList l val in
  -- trace ("Correct Value: " ++ show correctVal ++ "; computed Val: " ++ show testVal) $
  correctVal == testVal

rotateList :: [a] -> Int -> [a]
rotateList lst axis =
  let (pre, post) = splitAt axis lst in
  post ++ pre

searchLst :: [Int] -> Int -> Int
searchLst lst val =
  search lst 0 val
  where
    search (v:lst) n val = if v == val then n else search lst (n + 1) val
    search [] _ _ = -1

pureSearchRotatedList :: [Int] -> Int -> Int
pureSearchRotatedList lst val =
  if null lst then -1 else
  runST $ do
    arr <- newListArray (0, length lst - 1) lst :: ST s (STArray s Int Int)
    searchRotatedArray arr val

searchRotatedArray :: (MArray a Int m, Show b, Ix b, Integral b) => a b Int -> Int -> m b
searchRotatedArray arr val = do
  (min, max) <- getBounds arr
  let
    at i = readArray arr (min + i)
    len = max - min + 1
    preIdx i = if i <= 0 then len - 1 else i - 1
    -- first, find the rotate axis
    findAxis minId maxId
      -- if there is no such cliff within the place, it means no rotation happened
      | minId > maxId = return 0
      | minId == maxId = return minId
      | maxId - minId == 1 = do
        minPlaceVal <- at minId
        maxPlaceVal <- at maxId
        if minPlaceVal > maxPlaceVal then return maxId
        else return 0
      | otherwise = do
        let guess = (minId + maxId) `div` 2
        -- !_ <- trace ("Guessing place in finding axis: " ++ show guess ++ " with minId: " ++ show minId ++ " and maxId: " ++ show maxId) return ()
        thisVal <- at guess
        preVal <- at $ preIdx guess
        if preVal > thisVal then
          -- the guess place is the axis
          return guess
        else do
          -- find if it's over the axis or not-yet reach the axis
          minVal <- at minId
          if minVal < thisVal then
            -- not yet reached 
            findAxis guess maxId
          else
            -- over
            findAxis minId guess
  axis <- findAxis 0 $ len - 1
  !_ <- trace ("Axis Found: " ++ show axis) return ()
  let
    at i = readArray arr $ (axis + i) `mod` len
    idxOf i = (axis + i) `mod` len
    find minId maxId
      | minId > maxId = return $ -1
      | otherwise = do
        let guess = (minId + maxId) `div` 2
        -- !_ <- trace ("Guessing place: " ++ show guess ++ " with minId: " ++ show minId ++ " and maxId: " ++ show maxId) return ()
        thisVal <- at guess
        if val == thisVal then return $ idxOf guess
        else if val < thisVal then find minId (guess - 1)
        else find (guess + 1) maxId
  find 0 $ len - 1

-- =================================== Concate of Words ==============================

{-| return all the indices from which if one gets start, will first go through one kind of concat of all strings

>>> correctConcateOfWordBags "barfoothefoobarman" ["foo","bar"]
[0,9]
>>> correctConcateOfWordBags "wordgoodgoodgoodbestword" ["word","good","best","word"]
[]
>>> correctConcateOfWordBags "barfoofoobarthefoobarman" ["bar","foo","the"]
[6,9,12]
-}
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

{- Some ideas on a better implementation

firstly, generate a DFA, and then traverse from each of the start this DFA
so that for each time, it will just be of complexity O(m)

So, the total complexity is O(nm) where n for str, the maximum space complexity is O(n)
    -- for each position, there is a state keeper

Are there any better implementation that we can reuse the scanning results of n?
Shall we first scan n to find out all possible place for words?
Yes -- by DFA, we are able to do so.

So, we have a list of position information -- [(startPos, endPos + 1, wordIdx)]
    -- the same position may have multiple wordIdx
So, we then use bruteforce from here to see each case with this information.
Arrange this information by an array according to the startPostion -- an array of [(endPos + 1, wordIdx)]
  each position is a list because there maybe multiple words.
So, this is just a scan of the positions.
-}

-- testArray = 
--   runST $ do
--     arr <- newArray (1, 2) 0 :: ST s (STArray s Int Int)
--     readArray arr 1

-- ================================== Permutation Sequence =============================
-- get the kth sequence among permutation of [1..n]

testPermutationSequence :: Int -> Int -> Bool
testPermutationSequence n k =
  (n > 7) || (k <= 0) || (k > factorial n) || (
  let correctVal = correctPermutationSequence n k in
  let quickVal = quickPermutationSequence n k in
  -- trace ("For n = " ++ show n ++ "; k = " ++ show k ++ "; correct value = " ++ show correctVal ++ "; computed value = " ++ show quickVal) $
  correctVal == quickVal)

startTestPermutationSequence :: IO ()
startTestPermutationSequence = quickCheck testPermutationSequence

-- this is a easy cover test, better than the above test for n and k are definitely valid
quickTestPermutationSequence :: [a]
quickTestPermutationSequence = do
  n <- [1..7]
  k <- [1..factorial n]
  unless (testPermutationSequence n k) $
    error $ "Test failed with n = " ++ show n ++ "; k = " ++ show k
  []

allPermutationSequence :: (Ord a, Num a, Enum a) => a -> [[a]]
allPermutationSequence n = sort (arrange [1..n])

correctPermutationSequence :: Int -> Int -> [Int]
correctPermutationSequence n k =
  if n <= 0 || k <= 0 || k > factorial n then [] else
  sort (arrange [1..n]) !! (k - 1)

quickPermutationSequence :: Int -> Int -> [Int]
quickPermutationSequence n k =
  if n <= 0 || k <= 0 || k > factorial n then [] else
  qps [1..n] k
  where
    qps lst k =
      case lst of
        [] -> error "Undefined Behavior"
        [n] -> [n]
        lst ->
          let divider = factorial $ length lst - 1 in
          let (nth, nextK) = ((k - 1) `div` divider, (k - 1) `mod` divider) in
          let (pre, ~(h:post)) = splitAt nth lst in
          h : qps (pre ++ post) (nextK + 1)

-- =================================== n Queens ===================================

{-| extension of the famous 8 Queens question

>>> nQueens 4
[[3,1,4,2],[2,4,1,3]]
>>> length $ nQueens 8
92
-}
nQueens :: Int -> [[Int]]
nQueens n = do
  guard (n > 0)
  iter [] 1 []
  where
    iter :: [Int] -> Int -> [[Int]] -> [[Int]]
    iter record m res =
      -- trace ("record: " ++ show (zip [1..m - 1] $ reverse record)) $
      if m > n then record : res else
      foldr foldFunc res [1..n]
      where
        foldFunc toTest res =
          -- first, test if this position is OK
          if test toTest then iter (toTest : record) (m + 1) res
          else res
        test pos =
          pos `notElem` record &&
          and [m + pos /= i + v && m + n - pos /= i + n - v | (i, v) <- zip [1..m - 1] $ reverse record]


-- =================================== Spiral Order =================================

correctSpiralOrder :: [[a]] -> [a]
correctSpiralOrder matrix =
  if null matrix then [] else
  let n = length matrix in
  let m = length $ head matrix in
  let wellShape matrix = and [lenEq m line | line <- matrix] in
  if not $ wellShape matrix then error "Input Not of Well-Shape" else
  so (1, 1) n m
  where
    so (sx, sy) ln lm
      | ln <= 0 || lm <= 0 = []
      | ln == 1 =
        -- single line
        take lm $ drop (sy - 1) (matrix !! (sx - 1))
      | lm == 1 = do
        -- sinle column
        line <- take ln $ drop (sx - 1) matrix
        return $ line !! (sy - 1)
      | otherwise =
        let topLine = take lm $ drop (sy - 1) (matrix !! (sx - 1)) in
        let (leftColumn, rightColumn) = unzip $ do
              line <- take (ln - 2) $ drop sx matrix
              return (line !! (sy - 1), line !! (sy + lm - 2))
        in
        let bottomLine = take lm $ drop (sy - 1) (matrix !! (sx + ln - 2)) in
        topLine ++ rightColumn ++ reverse bottomLine ++ reverse leftColumn ++ so (sx + 1, sy + 1) (ln - 2) (lm - 2)

spiralOrder :: [[a]] -> [a]
spiralOrder matrix =
  if null matrix then [] else
  let n = length matrix in
  let m = length $ head matrix in
  let wellShape matrix = and [lenEq m line | line <- matrix] in
  if not $ wellShape matrix then error "Input Not of Well-Shape" else
  runST $ do
    mat <- newArray_ (1, n) :: ST s (STArray s Int (STArray s Int a))
    forM_ (zip [1..n] matrix) $ \(lineNum, line) -> do
      arr <- newListArray (1, m) line
      writeArray mat lineNum arr
    innerSpiralOrder mat (1, 1) n m
  where
    innerSpiralOrder matrix startState n m =
      if m <= 0 || n <= 0 then return [] else do
      let (xBase, yBase) = startState
      lst <- innerSpiralOrder matrix (xBase + 1, yBase + 1) (n - 2) (m - 2)
      retF <- newSTRef (++ [])
      idx <- newSTRef ((1, 1), True)
      cforM (isValid idx) (nextIdx idx) $ do
        ((x, y), _) <- readSTRef idx
        f <- readSTRef retF
        arr <- readArray matrix (x + xBase - 1)
        val <- readArray arr (y + yBase - 1)
        -- !_ <- trace ("here, x = " ++ show (x + xBase - 1) ++ "; y = " ++ show (y + yBase - 1) ++ "; value = " ++ show val) return ()
        writeSTRef retF (\x -> f (val : x))
      f <- readSTRef retF
      return $ f lst
      where
        isValid idx = do
          ((x, y), b) <- readSTRef idx
          return $ b || (y > 1 && x >= 1 || y >= 1 && x > 1) && x <= n && y <= m
        nextIdx (idx :: STRef s ((Int, Int), Bool)) = do
          ((x, y), b) <- readSTRef idx
          -- !_ <- trace ("Var = " ++ show var) return ()
          writeSTRef idx $ (($ False) . (,)) $
            if x == 1 && y == 1 && not b then (0, 0)
            else if x == 1 && y < m then (x, y + 1)
            else if y == m && x < n then (x + 1, y)
            else if x == n && y > 1 then (x, y - 1)
            else if y == 1 && x > 1 then (x - 1, y)
            else if x == 1 && y == 1 && b then (x + 1, y)
            else error "Impossible"

-- ===================================== Can Jump to End ==================================

{-| 

>>> canJumpToEnd [3,2,1,0,4]
False
-}
canJumpToEnd :: [Int] -> Bool
canJumpToEnd lst =
  cjte lst (length lst - 1)
  where
    cjte :: [Int] -> Int -> Bool
    cjte []      _ = False
    cjte (h:lst) leftLenToEnd =
      trace ("lst = " ++ show (h:lst) ++ "; leftLenToEnd = " ++ show leftLenToEnd) call
      where
        call
          | h <= 0 = False  -- by definition, can never reach the end
          | h > leftLenToEnd = False
          | h == leftLenToEnd = True
          | otherwise = cjte (drop (h - 1) lst) (leftLenToEnd - h)

-- ====================================== Matrix Product ==================================

matrixProd :: (Monad m, Num b) => m [b] -> [[b]] -> m [b]
matrixProd m1 m2 = do
  line <- m1;
  return $ (\column -> sum $ uncurry (*) <$> zip line column) <$> transpose m2

matrixProd' :: Num b => [[b]] -> [[b]] -> [[b]]
matrixProd' m1 m2 =
  runST $
    forM [0..length m1 - 1] $ \line ->
      forM [0..length (head m2) - 1] $ \column -> do
        valCell <- newSTRef 0
        forM_ [0..length m2 - 1] $ \idx -> do
          val <- readSTRef valCell
          writeSTRef valCell (val + (m1 !! line !! idx * m2 !! idx !! column))
        readSTRef valCell

newtype Matrix d = Matrix [[d]] deriving (Show)
newtype MatrixPair d = MatrixPair (Matrix d, Matrix d) deriving (Show)

instance (Arbitrary d) => Arbitrary (MatrixPair d) where
  -- | method to generate a pair of matrices that are ready to be tested
  arbitrary = do
    (ln :: Int) <- arbitrary
    (md :: Int) <- arbitrary
    (col :: Int) <- arbitrary
    let line = abs ln
    let middle = abs md
    let column = abs col
    if line <= 0 || middle <= 0 || column <= 0 then return $ MatrixPair (Matrix [], Matrix [])
    else do
      mat1 <- genMatrix line middle
      mat2 <- genMatrix middle column
      return $ MatrixPair (Matrix mat1, Matrix mat2)
    where
      genMatrix line column =
        if line <= 0 then return [] else do
          ln <- genLine column
          mat <- genMatrix (line - 1) column
          return $ ln : mat
        where
          genLine 0 = return []
          genLine n = do
            (val :: d) <- arbitrary
            line <- genLine (n - 1)
            return $ val : line

testMatrixProd :: MatrixPair Int -> Bool
testMatrixProd (MatrixPair (Matrix m1, Matrix m2)) =
  null m1 || null m2 ||
  -- trace ("Scale = (" ++ show (length m1) ++ 
  --   " * " ++ show (length $ head m1) ++ ") * (" ++ show (length m2) ++ " * " ++ show (length $ head m2) ++ ")")
  matrixProd m1 m2 == matrixProd' m1 m2

quickTestMatrixProd = quickCheck testMatrixProd

-- ======================================== Is Scramble String ====================================

newtype LowerCaseEnglishString = LowerCaseEnglishString String deriving (Show)

instance Arbitrary LowerCaseEnglishString where
  arbitrary = do
    (ASCIIString str) <- arbitrary
    return $ LowerCaseEnglishString [x | x <- str, let xidx = fromEnum x, xidx >= fromEnum 'a', xidx <= fromEnum 'z']

-- >>> scrambleStrings "abc"
-- ["abc","bca","acb","cba","abc","cab","bac","cba"]
scrambleStrings :: String -> [String]
scrambleStrings str =
  case str of
    [] -> []
    [a] -> [[a]]
    _ -> do
      idx <- [1..length str - 1]
      let (pre, post) = splitAt idx str
      prs <- scrambleStrings pre
      pos <- scrambleStrings post
      [prs ++ pos, pos ++ prs]

correctIsScrambleString :: String -> String -> Bool
correctIsScrambleString s str =
  length s == length str && (s `elem` Set.fromList (scrambleStrings str))

{-| Ideas on a quicker implementation

it can only become smaller, so, traver all places that can be matched -- with the same set of elements
to find the first division point
and then for the left, do the same.
Because it is multi-set, it should be map rather than set
For each of this process, it is of O(n) complexity
so, it should be O(n^2)
-}
-- -- >>> testHashTable
-- testHashTable :: Maybe Int
-- testHashTable =
--   runST $ do
--   tab <- HashTable.new :: ST s (HashTable.HashTable s Int Int)
--   HashTable.insert tab 1 1
--   HashTable.lookup tab 2

-- | this quick method currently only for lowercase English string, other invalid input will cause a collapse
isScrambleString :: LowerCaseEnglishString -> LowerCaseEnglishString -> Bool
isScrambleString (LowerCaseEnglishString s) (LowerCaseEnglishString str) =
  runST $ do
    let lenS = length s
    let lenStr = length str
    sArr <- newListArray (1, length s) s :: ST s (STArray s Int Char)
    strArr <- newListArray (1, length str) str :: ST s (STArray s Int Char)
    findVal (sArr, (1, lenS)) (strArr, (1, lenStr))
  where
    -- clearHashTable tab = HashTable.mapM_ (\(k, v) -> HashTable.mutate tab k (const (Just 0, ()))) tab
    -- find tab key = HashTable.mutate tab key $ \case { Nothing -> (Just 0, 0); Just v  -> (Just v, v) }
    compareArr arr1 arr2 = do
      (min, max) <- getBounds arr1
      (mn, mx) <- getBounds arr2
      if max - min + 1 /= mx - mn + 1 then return False else
        fmap and $ forM [0..max - min] $ \idx ->
          (==) <$> readArray arr1 (min + idx) <*> readArray arr2 (mn + idx)
    incMap arr c = do
      let idx = fromEnum c - fromEnum 'a'
      val <- readArray arr (1 + idx)
      writeArray arr (1 + idx) (val + 1)
    findVal :: (STArray s Int Char, (Int, Int)) -> (STArray s Int Char, (Int, Int)) -> ST s Bool
    findVal (sArr, (minS, maxS)) (strArr, (minStr, maxStr)) =
      -- for length <= 3, the result is yes
      if maxS - minS + 1 <= 3 then return True else do
        -- as we only test for lower case English letters, we can use 26-position array
        -- sFront <- HashTable.new :: ST s (HashTable.HashTable s Char Int)
        -- sBack <- HashTable.new :: ST s (HashTable.HashTable s Char Int)
        -- strMap <- HashTable.new :: ST s (HashTable.HashTable s Char Int)
        sFront <- newArray (1, 26) 0 :: ST s (STArray s Int Int)
        sBack <- newArray (1, 26) 0 :: ST s (STArray s Int Int)
        strMap <- newArray (1, 26) 0 :: ST s (STArray s Int Int)
        result <- newSTRef False
        -- to length - 2, because to the end may cause infinite looping
        forM_ [0..maxS - minS - 1] $ \idx -> do
          res <- readSTRef result
          if res then return () else do
            -- increse map values according to the new value
            incMap sFront =<< readArray sArr (minS + idx)
            incMap sBack =<< readArray sArr (maxS - idx)
            incMap strMap =<< readArray strArr (minStr + idx)
            whenM (compareArr strMap sFront) $ do
              -- this index is a possible breaking point, and the order is front-back
              whenM (findVal (sArr, (minS, idx + minS)) (strArr, (minStr, idx + minStr))) $   -- break if not
                whenM (findVal (sArr, (idx + minS + 1, maxS)) (strArr, (idx + minStr + 1, maxStr))) $   -- break if not
                  writeSTRef result True
            whenM (not <$> readSTRef result) $ -- if result is yes, just break and return
              whenM (compareArr strMap sBack) $
                -- this index is a possible breaking point, and the order is back-front
                whenM (findVal (sArr, (maxS - idx, maxS)) (strArr, (minStr, idx + minStr))) $
                  whenM (findVal (sArr, (minS, maxS - idx - 1)) (strArr, (idx + minStr + 1, maxStr))) $
                    writeSTRef result True
        readSTRef result

testIsScrambleString :: LowerCaseEnglishString -> Bool
testIsScrambleString str@(LowerCaseEnglishString stri) =
  ((length stri > 30 || null stri) ||) $ and $ do
  trace ("Testing str = " ++ stri) return ()
  si <- arrange stri
  trace ("Testing s = \"" ++ si ++ "\" with str = \"" ++ stri ++ "\"") return ()
  let s = LowerCaseEnglishString si
  let correctResult = si `correctIsScrambleString` stri
  trace "correct result obtained" return ()
  let targetResult = s `isScrambleString` str
  trace "target result obtained" return ()
  let res = targetResult == correctResult
  if not res then
    error ("test error s = \"" ++ si ++ "\" with str = \"" ++ stri ++ "\"")
  else
  -- unless res $ trace ("test error s = \"" ++ si ++ "\" with str = \"" ++ stri ++ "\"") return ()
    return res

-- | Already went through sufficient tough test
quickTestIsScrambleString :: IO ()
quickTestIsScrambleString = quickCheck testIsScrambleString


-- ======================================= Minimum Window Substring =======================================

{-| returns Maybe (startingPoint, length)

startingPoint from 0

>>> correctMinimumWindowSubstring "a" "a"
Just (0,1)

>>> correctMinimumWindowSubstring "ADOBECODEBANC" "ABC"
Just (9,4)
-}
correctMinimumWindowSubstring :: (Ord b, Num b, Eq a) => [a] -> [a] -> Maybe (Int, b)
correctMinimumWindowSubstring str1 str2 =
  let len1 = length str1 in
  let len2 = length str2 in
  if null str2 || len2 > len1 then Nothing else
  let getLen :: (Num r, Eq a) => [a] -> [a] -> Maybe r
      getLen _  []     = Just 0
      getLen [] _      = Nothing
      getLen (h:s) str = fmap (+1) $ getLen s $ if h `elem` str then str \\ [h] else str
      resLst           = do idx <- [0..len1 - len2]
                            let lst = drop idx str1
                            let len = getLen lst str2
                            if isNothing len then [] else return (idx, fromJust len)
  in
  if null resLst then Nothing else Just $ minimumBy (\x y -> compare (snd x) (snd y)) resLst

{-| A quicker version 

startingPoint from 0

>>> minimumWindowSubstring "a" "a"
Just (0,1)

>>> minimumWindowSubstring "ADOBECODEBANC" "ABC"
MArray: undefined array element
-}
minimumWindowSubstring :: (Hashable a, Ord a) => [a] -> [a] -> Maybe (Int, Int)
minimumWindowSubstring str1 str2 =
  let len1 = length str1 in
  let len2 = length str2 in
  if null str2 || len2 > len1 then Nothing else
  runST $ do
  -- arrStr1 <- newArray_ (1, len1) :: ST s (STArray s Int a)
  arrStr1 <- (newListArray (1, len1) :: [a] -> ST s (STArray s Int a)) str1
  -- arrStr1 <- newListArray (1, len1) str1 :: ST s (STArray s Int a)
  map <- HashTable.new
  leftCount <- newSTRef len2
  forM_ str2 $ \c -> HashTable.mutate map c $ \case {Just v -> (Just $ v - 1, ()); Nothing -> (Just $ -1, ())}
  -- record the next position to prob
  toProb <- newArray_ (0, len1 - 1) :: ST s (STArray s Int Int)
  toProbLength <- newSTRef 0
  idx <- newSTRef 1  -- use 1..len1
  -- find the first segment
  cforM ((&&) . (>0) <$> readSTRef leftCount <*> ((<=len1) <$> readSTRef idx))
        (modifySTRef idx (+1)) $ do
    i <- readSTRef idx
    c <- readArray arrStr1 i
    HashTable.mutateST map c $ \case
      -- not in str2
      Nothing -> return (Nothing, ())
      -- inside str2
      Just v -> do
        when (v < 0) $ modifySTRef leftCount (\x -> x - 1)
        readSTRef toProbLength >>= \len -> writeArray toProb len i
        modifySTRef toProbLength (+1)
        return (Just $ v + 1, ())
  -- val <- readArray toProb 0
  -- first segment found
  -- record the current result
  result <- newSTRef Nothing
  whenM ((<0) <$> readSTRef leftCount) $ error "Unexpected Happened"
  whenM ((==0) <$> readSTRef leftCount) $ do
    firstIdx <- readArray toProb 0
    -- idx has now pointed to the next place to inspect
    readSTRef idx >>= \i -> writeSTRef result $ Just (firstIdx, i - firstIdx)
    -- create an observer
    obsIdx <- newSTRef 0
    -- initialise the observe information
    -- take out and increase leftCount while possibly updating the result
    let
      -- | update the result, just provide the front index reference, update will be performed with current index
      updateResult = do
        fId <- readArray toProb =<< readSTRef obsIdx
        -- idx should now point to the next index when updating
        nextId <- readSTRef idx
        let newLen = nextId - fId
        modifySTRef result $ \ ~ori@(Just (_, len)) -> if newLen < len then return (fId, newLen) else ori
      takeNextAndIncrease =
        whileM ((==0) <$> readSTRef leftCount) $ do
        obsId <- readSTRef obsIdx
        modifySTRef obsIdx (+1)
        tarC <- readArray arrStr1 =<< readArray toProb obsId
        HashTable.mutateST map tarC $ \ ~(Just v) -> do
          -- if (v - 1 < 0) this means that some holes must be filled
          if v - 1 < 0 then modifySTRef leftCount (+1) else updateResult
          -- otherwise, this means that there is some others behind, so just update the result
          return (Just $ v - 1, ())
    takeNextAndIncrease
    cforM ((<=len1) <$> readSTRef idx) (modifySTRef idx (+1)) $ do -- if no, just break, otherwise, continue 
      -- in this outter loop, first need to take out one 
      thisC <- readArray arrStr1 =<< readSTRef idx
      HashTable.mutateST map thisC $ \case
        Nothing -> return (Nothing, ())
        Just v  -> do
          when (v + 1 < 0) $ error "Impossible Case: v should be at least -1"
          when (v + 1 == 0) $ do
            -- newly done
            modifySTRef leftCount (\x -> x - 1)
            updateResult
            takeNextAndIncrease
          return (Just $ v + 1, ())
  modifySTRef result $ fmap $ \(v, len) -> (v - 1, len)
  readSTRef result


-- ==================================== Megerge Interval ===================================

-- >>> normaliseIntervals [(0,0),(0,-1)]
-- [(0,0),(-1,0)]
normaliseIntervals :: (Functor f, Ord b) => f (b, b) -> f (b, b)
normaliseIntervals = fmap $ \(mn, mx) -> (min mn mx, max mn mx)

isValidIntervals :: Ord a => [(a, a)] -> Bool
isValidIntervals intervals =
  and [ min <= max | (min, max) <- intervals ]

noOverlap :: Ord a => [(a, a)] -> Bool
noOverlap [] = True
noOverlap ((cmin, cmax):rst) =
  (noOverlap rst &&) $ and $ do
    (min, max) <- rst
    if cmin < min then return $ cmax < min
    else if cmin == min then return False
    else return $ max < cmin

coverByIntervals :: Ord a => [(a, a)] -> a -> Bool
coverByIntervals intervals num =
  or [ num <= max && num >= min | (min, max) <- intervals ]

-- >>> mergeIntervals [(0,0),(-1,0)]
-- [(-1,0)]
-- | Test Passed
mergeIntervals :: (Ord a) => [(a, a)] -> [(a, a)]
mergeIntervals intervals =
  if null intervals then [] else
  uncurry (:) $
  let sortedIntervals = sortOn fst intervals in
  foldl
    (\(cpair@(cmin, cmax), resLst) tpair@(tmin, tmax) ->
      if cmax >= tmin then ((cmin, max cmax tmax), resLst) else (tpair, cpair:resLst))
    (head sortedIntervals, [])
    sortedIntervals

firstTestMergeIntervals :: [(Int, Int)] -> Bool
firstTestMergeIntervals (l :: [(Int, Int)]) =
  noOverlap $ mergeIntervals $ normaliseIntervals l

secondTestMergeIntervals :: [(Int, Int)] -> Int -> Bool
secondTestMergeIntervals l num =
  let lst = normaliseIntervals l in
  let correctResult = coverByIntervals lst num in
  let obtainedResult = coverByIntervals (mergeIntervals lst) num in
  correctResult == obtainedResult

-- ======================================== Insert Interval ====================================

correctInsertInterval :: Ord a => [(a, a)] -> (a, a) -> [(a, a)]
correctInsertInterval intervals newInterval =
  mergeIntervals (newInterval : intervals)

-- non-overlapping intervals
-- | test passed
insertInterval :: Ord a => [(a, a)] -> (a, a) -> [(a, a)]
insertInterval intervals el =
  ii (sortOn fst intervals) el
  where
    ii [] el = [el]
    ii (cel@(cmin, cmax) : rst) tar@(tmin, tmax)
      | cmax < tmin = cel : insertInterval rst tar
      | tmax < cmin = tar : cel : rst
      | otherwise =  -- overlapping
        insertInterval rst (min tmin cmin, max tmax cmax)

testInsertInterval :: [(Int, Int)] -> (Int, Int) -> Bool
testInsertInterval lst (cmin, cmax) =
  let l = mergeIntervals $ normaliseIntervals lst in
  let tel = (min cmin cmax, max cmin cmax) in
  sort (correctInsertInterval l tel) == sort (insertInterval l tel)


-- ===================================== Distinct Subsequences =====================================

-- >>> distinctSequences "rabbbit" "rabbit"
-- 3
-- >>> distinctSequences "babgbag" "bag"
-- 5
-- >>> distinctSequences "aaaaaaaaaaaaaaaa" "a"
-- 16

-- | A faster C++ version: use map to save repeat computation, also, if length s < length t, quit
distinctSequences :: (Num p, Eq a) => [a] -> [a] -> p
distinctSequences _s [] = 1
distinctSequences [] _ = 0
distinctSequences (s:ss) tt@(h:t) =
  if s == h then distinctSequences ss tt + distinctSequences ss t
  else distinctSequences ss tt


-- ============================ Remove Duplicate Elements ============================

-- >>> removeDuplicateElements [1,2,3,3,4,4,5]
-- [1,2,5]
-- >>> removeDuplicateElements [1,1,1,2,3]
-- [2,3]
removeDuplicateElements :: Eq a => [a] -> [a]
removeDuplicateElements [] = []
removeDuplicateElements [x] = [x]
removeDuplicateElements (x : y : lst) =
  if x == y then
    case removeDuplicateElements (y : lst) of
      []       -> []
      y' : lst -> if x == y' then lst else y' : lst
  else x : removeDuplicateElements (y : lst)


-- ================================ Word Ladder ================================

-- >>> wordLadder "hit" "cog" ["hot","dot","dog","lot","log","cog"]
-- ["hit","hot","dot","dog","cog"]

-- >>> wordLadder "hit" "cog" ["hot","dot","dog","lot","log"]
-- []

wordLadder :: Eq a => [a] -> [a] -> [[a]] -> [[a]]
wordLadder this target wrdLst
  | target `notElem` wrdLst = []
  | otherwise = wl this target $ wrdLst \\ [target]
  where
    difTo1 this target =
      foldl (\s (x, y) -> s + if x == y then 0 else 1) 0 (zip this target) == 1
    wl this tar lst
      | difTo1 this tar = [this, tar]
      | otherwise =
        foldl (\l n -> if null l || length l > length n then n else l) [] $ do
          lst <- [ wl this nTar $ lst \\ [nTar] | nTar <- lst, difTo1 tar nTar ]
          if null lst then [] else return $ lst ++ [tar]


-- ================================== Decode Ways ================================

decodeWays :: String -> Int
decodeWays = length . filter (not . null) . possibleDecodes

-- >>> possibleDecodes "11106"
-- [[1,1,10,6],[11,10,6]]

-- >>> possibleDecodes "110"
-- [[1,10]]

-- >>> possibleDecodes "226"
-- [[2,2,6],[2,26],[22,6]]
possibleDecodes :: String -> [[Int]]
possibleDecodes = \case
  []                                     -> [[]]
  [x] | isNumber x && decodeNumber x > 0 -> [return $ decodeNumber x]
  x : y : lst | isNumber x && isNumber y ->
    case (decodeNumber x, decodeNumber y) of
      (x, 0) | x == 1 || x == 2 ->
        [ (10 * x) : str | str <- possibleDecodes lst ]
      (x, y') | x == 1 || (x == 2) && y' <= 6 ->
        [ x : str | str <- possibleDecodes (y : lst) ] ++
        [ (10 * x + y') : str | str <- possibleDecodes lst ]
      (0, _) -> []
      (x, _) ->
        [ x : str | str <- possibleDecodes (y : lst) ]
  _ -> []
  where
    isNumber x = (0, 9) `inRange` decodeNumber x
    decodeNumber x = fromEnum x - fromEnum '0'
    _convertToChar x = toEnum $ x + fromEnum 'A' + 1

possibleDecodesWays :: String -> Maybe Integer
possibleDecodesWays = \case
  []                                     -> Just 0
  [x] | isNumber x && decodeNumber x > 0 -> Just 1
  x : y : lst | isNumber x && isNumber y ->
    case (decodeNumber x, decodeNumber y) of
      (x, 0) | x == 1 || x == 2 -> (+1) <$> possibleDecodes lst
      (x, y') | x == 1 || (x == 2) && y' <= 6 ->
        case ((+1) <$> possibleDecodes (y : lst),
              (+1) <$> possibleDecodes lst) of
          (Just x, Just y) -> return $ x + y
          (Nothing, y)     -> y
          (x, Nothing)     -> x
      (0, _) -> Nothing
      (_, _) -> (+1) <$> possibleDecodes lst
  _ -> Nothing
  where
    possibleDecodes = possibleDecodesWays
    isNumber x = (0, 9) `inRange` decodeNumber x
    decodeNumber x = fromEnum x - fromEnum '0'
    _convertToChar x = toEnum $ x + fromEnum 'A' + 1

quickDecodeWays :: String -> Integer
quickDecodeWays = fromMaybe 0 . possibleDecodesWays

newtype NumChar = NumChar Char deriving (Show)

instance Arbitrary NumChar where
  arbitrary = do
    int <- arbitrary
    return $ NumChar $ toEnum $ int `mod` 10

-- prop> testDecodeWays
-- +++ OK, passed 100 tests.
testDecodeWays :: [NumChar] -> Bool
testDecodeWays (lst :: [NumChar]) =
  let str :: String = fmap (\(NumChar c) -> c) lst in
  decodeWays str == fromInteger (quickDecodeWays str)


-- ===================================== Word Break =====================================

-- >>> wordBreak "catsanddog" ["cat","cats","and","sand","dog"]
-- [["cat","sand","dog"],["cats","and","dog"]]

-- >>> wordBreak "pineapplepenapple" ["apple","pen","applepen","pine","pineapple"]
-- [["pine","apple","pen","apple"],["pine","applepen","apple"],["pineapple","pen","apple"]]

-- >>> wordBreak "catsandog" ["cats","dog","sand","and","cat"]
-- []
wordBreak :: Eq a => [a] -> [[a]] -> [[[a]]]
wordBreak []  _   = [[]]
wordBreak str dic = do
  word <- [ word | word <- dic, word `isPrefixOf` str ]
  res  <- wordBreak (drop (length word) str) dic
  return $ word : res


-- =================================== Candy Least Dist =====================================

-- https://leetcode.com/problems/candy/

candy :: (Num a, Ord a2, Ord a) => [a2] -> a
candy = sum . candyLeastDist

-- >>> candyLeastDist [1,2,2]
-- [1,2,1]

-- >>> candyLeastDist [1,0,2]
-- [2,1,2]
candyLeastDist :: (Num a1, Ord a2, Ord a1) => [a2] -> [a1]
candyLeastDist [] = []
candyLeastDist [_] = [1]
candyLeastDist (x : lst@(y : _)) =
  let ~res@(hd:_) = candyLeastDist lst in
  if x > y then hd + 1 : res
  else if x == y || hd > 1 then 1 : res
  else -- x < y && hd == 1
      1 : propagateInc res lst
  where
    propagateInc :: (Num a, Ord b) => [a] -> [b] -> [a]
    propagateInc [x] [_] = [x + 1]
    propagateInc (x:xs) (y:ys@(ny:_)) = x + 1 : if y < ny then propagateInc xs ys else xs
    propagateInc _ _ = error "Impossible"

validCandyDist :: (Ord a1, Ord a2) => [a2] -> [a1] -> Bool
validCandyDist [] []   = True
validCandyDist [_] [_] = True
validCandyDist (x:xs@(nx:_)) (y:ys@(ny:_))
  | y > ny = x > nx && validCandyDist xs ys
  | y < ny = x < nx && validCandyDist xs ys
  | otherwise = validCandyDist xs ys
validCandyDist _ _ = undefined

-- prop> testCandyLeastDist
-- +++ OK, passed 100 tests.
testCandyLeastDist :: [Int] -> Bool
testCandyLeastDist lst =
  validCandyDist (candyLeastDist lst) lst

-- =================================== Palindrome Partition ===================================

-- >>> isPalindrome "a"
-- True

-- >>> isPalindrome "aba"
-- True

-- >>> isPalindrome "abb"
-- False
isPalindrome :: Eq a => [a] -> Bool
isPalindrome lst =
  let (x, y) = splitAt (length lst `div` 2) lst in
  all (uncurry (==)) $ zip x $ reverse y

-- >>> palindromePartition "ab"
-- [["a","b"]]
palindromePartition :: Eq a => [a] -> [[[a]]]
palindromePartition lst =
  case lst of
    []    -> []
    [x]   -> [[[x]]]
    x:lst -> do
      ~(hd:res) <- palindromePartition lst
      let fst = ([x]:hd:res) : [(x:hd):res | isPalindrome (x:hd)]
      case res of
        [y]:rst -> if x == y then ((x:hd ++ [y]):rst):fst else fst
        _       -> fst

-- prop> testPalindromePartitionProp
-- +++ OK, passed 100 tests.
testPalindromePartitionProp :: String -> Bool
testPalindromePartitionProp = all (all isPalindrome) . palindromePartition

-- >>> allPartition "ab"
-- [["ab"],["a","b"]]
allPartition :: [a] -> [[[a]]]
allPartition [] = []
allPartition [x] = [[[x]]]
allPartition (x:lst) = do
  ~(hd:res) <- allPartition lst
  [(x:hd):res, [x]:hd:res]

correctPalindromePartition :: Eq a => [a] -> [[[a]]]
correctPalindromePartition lst = [ par | par <- allPartition lst, all isPalindrome par]

-- prop> testPalindromePartition
testPalindromePartition :: String -> Bool
testPalindromePartition lst =
  unique (palindromePartition lst) == unique (correctPalindromePartition lst)


class Graph t where
  initVertices :: t v -> [v]
  nextVertices :: v -> t v -> [v]

-- | returns a DFS visit to all vertices in the graph
dfsOrder :: (Graph t, Eq v) => t v -> [v]
dfsOrder graph =
  foldl foldFunc [] $ initVertices graph
  where
    foldFunc visited v
      | v `elem` visited = visited
      | otherwise        = foldl foldFunc (v : visited) $ nextVertices v graph


-- ====================================== Dominoes =================================
-- a question from https://exercism.org/tracks/haskell/exercises/dominoes 
-- give a list of dominoes 

-- >>> oneAndRest [(2, 1), (2, 3), (1, 3)]
-- [((2,1),[(2,3),(1,3)]),((2,3),[(2,1),(1,3)]),((1,3),[(2,1),(2,3)])]
oneAndRest :: [a] -> [(a, [a])]
oneAndRest lst = [ (p, f ++ l) | i <- [0..length lst - 1], let (f, s) = splitAt i lst, let ~(p:l) = s ]

-- >>> dominoes [(2, 1), (2, 3), (3, 1)]
-- [[(2,1),(1,3),(3,2)],[(1,2),(2,3),(3,1)],[(2,3),(3,1),(1,2)],[(3,2),(2,1),(1,3)],[(3,1),(1,2),(2,3)],[(1,3),(3,2),(2,1)]]
dominoes :: Eq a => [(a, a)] -> [[(a, a)]]
dominoes [] = []
dominoes lst =
  [ can | (x, xs) <- oneAndRest lst,
          can <- dominoCandidates x xs ++ dominoCandidates (swap x) xs,
          fst (head can) == snd (last can) ]

-- | the candidate dominos that starts from the first element
dominoCandidates :: Eq a => (a, a) -> [(a, a)] -> [[(a, a)]]
dominoCandidates x [] = [[x]]
dominoCandidates p@(_, b) lst = do
  (np@(a', b'), lst) <- oneAndRest lst
  let va = [ p : nl | b == a', nl <- dominoCandidates np lst ]
  let vb = [ p : nl | b == b', nl <- dominoCandidates (swap np) lst ]
  va ++ vb

testWork :: IO ()
testWork = do
  putStrLn "Please Input"
  str <- getLine
  putStrLn $ "Cur: " ++ str


-- ============================================ Dungeon Game ======================================

{-| Quesion in https://leetcode.com/problems/dungeon-game/

Compute the least HP the hero needs from left top to right bottom corner

gives the dungeon map which is a matrix of damage or bonus value

returns the least HP and the corresponding movement of the dungeon
  - 'R' for right
  - 'D' for down
  - 'T' for reaching the target

Examples: 

>>> dungeonGame [[-2,-3,3],[-5,-10,1],[10,30,-5]]
Just (7,"RRDDT")

>>> dungeonGame [[0]]
Just (1,"T")

>>> dungeonGame [[10]]
Just (1,"T")
-}
dungeonGame :: (Ord a, Num a) => [[a]] -> Maybe (a, [Char])
dungeonGame dungeonMap =
  if not $ shapeValid dungeonMap then Nothing else
  dungeonTrajectories dungeonMap
  |> fmap leastHealthPoint
  |> return . minimumWith fst
  where
    dungeonTrajectories []  = []
    dungeonTrajectories [[x]] = [[(x, 'T')]]  -- Target here, no further move
    dungeonTrajectories map
      | null $ head map = []
      | otherwise =
        [ (head (head map), 'R') : lst | lst <- dungeonTrajectories $ fmap tail map ] ++
        [ (head (head map), 'D') : lst | lst <- dungeonTrajectories $ tail map ]
    leastHealthPoint lst =
      let (toCope, secondPart) = unzip lst in
      let firstPart = fst $ flip (`foldl` (0, 0)) toCope $ \(minVal, cur) next ->
                        let nextCur = cur + next in
                        (min minVal nextCur, nextCur) in
      -- let firstPart = minimum [ sum x | x <- inits toCope, not $ null x ] in 
      (1 - firstPart, secondPart)
    -- | must be not null matrix
    shapeValid []    = False
    shapeValid map   = let len = length $ head map in
                       len > 0 && all (lenEq len) map


-- ====================================== Sliding Window Maximum ======================================

-- >>> slidingWindowMaximum [1,3,-1,-3,5,3,6,7] 3
-- [3,3,5,5,6,7]
slidingWindowMaximum :: Ord a => [a] -> Int -> [a]
slidingWindowMaximum nums winSize =
  [ maximum $ take winSize win | win <- tails nums, length win >= winSize ]

quickSlidingWindowMaximum :: Ord a => [a] -> Int -> [a]
quickSlidingWindowMaximum nums winSize =
  if winSize <= 0 then [] else
  let (initLst, rest) = splitAt winSize nums in
  performCompute initLst rest
  where
    performCompute hds rst =
      maximum hds : if null rst then [] else performCompute (tail hds ++ [head rst]) $ tail rst


validNumber :: [Char] -> Maybe Rational
validNumber str =
  let lst = readsPrec 1 str in
  if length lst /= 1 then Nothing else return $ fst $ head lst

quickTwoSum lst target =
  runST $ do
  tab <- HashTable.new
  flip (`foldM` Nothing) (zip lst [0..]) $ \maybe (n, i) -> do
    if isJust maybe then return maybe else do
      let m = target - n
      ifIdx <- HashTable.lookup tab m
      if isJust ifIdx then return $ return (fromJust ifIdx, i) else do
        HashTable.insert tab n i
        return Nothing

twoSum lst target =
  let l = zip [0..] lst in
  listToMaybe [ (n, m) | (n, num) <- l, (m, num') <- l, n /= m, num + num' == target ]

-- This data structure is also compatible with lambda term
data ExprTree at = ETAtom at | ETBranch [ExprTree at] deriving (Show)

parseExprTree :: (t -> at) -> ExprTree t -> ExprTree at
parseExprTree parse tree =
  case tree of
    ETAtom  at   -> ETAtom $ parse at
    ETBranch brs -> ETBranch $ fmap (parseExprTree parse) brs

-- | parse an S Expression to its AST of String
-- for further parse, just recursively parse the string inside using 
-- the above `parseExprTree` function
parseSExpr :: String -> Maybe (ExprTree String)
parseSExpr str =
  let tok = lexicalStream lex str in
  if null tok then Nothing else do
    tok <- checkValid tok
    res <- parse tok []
    -- due to the order of parsing, the result obtained will be reversed
    -- so we should reverse it recursively to obtain the right result
    return $ revRes res
  where
    revRes :: ExprTree at -> ExprTree at
    revRes (ETBranch br) = ETBranch $ reverse $ fmap revRes br
    revRes x@(ETAtom _)  = x

    checkValid :: [String] -> Maybe [String]
    checkValid tok = do
      val <- checkParenBalance tok 0
      if val == 0 then return tok else Nothing

    checkParenBalance :: (Num a, Ord a) => [String] -> a -> Maybe a
    checkParenBalance [] curBalance = return curBalance
    checkParenBalance (x:xs) curBalance =
      case x of
        "(" -> checkParenBalance xs (curBalance + 1)
        ")" ->
          if curBalance <= 0 || (curBalance == 1 && not (null xs)) then Nothing
          else checkParenBalance xs (curBalance - 1)
        _   -> checkParenBalance xs curBalance

    parse :: [String] -> [ExprTree String] -> Maybe (ExprTree String)
    parse [] [x] = Just x
    parse [] _   = Nothing
    parse (x:xs) tok =
      case x of
        "(" -> parse xs (ETBranch [] : tok)
        ")" ->
          case tok of
            [x] -> parse xs [x]
            x:(ETBranch ys):ss -> parse xs (ETBranch (x:ys) : ss)
            _ -> error "Impossible"
        x   ->
          case tok of
            (ETBranch ys):ss -> parse xs (ETBranch (ETAtom x:ys):ss)
            _                -> error "Impossible"


-- ======================================= Count Digit 1 =======================================

-- >>> countBits1 (6 :: Integer)
-- 9
countBits1 :: Integer -> Integer
countBits1 num
  | num <= 0  = 0
  | otherwise = countBit1s num + countBits1 (num - 1)

countBit1s :: Integer -> Integer
countBit1s num
  | num <= 0  = 0
  | otherwise = num Data.Bits..&. 1 + countBit1s (shift num (-1))

printBinary :: (Integral a, Show a) => a -> String
printBinary num = showIntAtBase 2 intToDigit num ""

anotherCountBits1 :: (Integral a, Show a) => a -> Int
anotherCountBits1 num
  | num <= 0  = 0
  | otherwise = length [ c | c <- printBinary =<< [0..num], c == '1']

-- >>> countDigit1 1234
-- 689
countDigit1 :: Int -> Int
countDigit1 num
  | num <= 0  = 0
  | otherwise = length [c | c <- show =<< [0..num], c == '1']

-- >>> newTry 0.5 0.25 0.25 :: Rational
-- 2 % 31
newTry :: Fractional a => a -> a -> a -> a
newTry pA pB pC = (pA * pB * pC) / ((1 - pA) * (1 - pA * pB * pC))

-- >>> pahorsSupportCompute 0.3 0.2
-- 0.32055052822966335
pahorsSupportCompute :: Floating a => a -> a -> a
pahorsSupportCompute p1 p2 = (1 - sqrt (1 - 4 * p1 * p2)) / 2 / p2

-- >>> pahorsSupport2 0.7 0.2 0.1 :: Rational
-- 7 % 493
pahorsSupport2 :: Fractional a => a -> a -> a -> a
pahorsSupport2 pA pB pC = (pA * pB * pC) / (1 - pA * pB * pC)

testGetN :: Int -> Bool
testGetN n =
  trace ("Testing " ++ show n) $
  getN n == correctGetN n

-- prop> \n -> getN n == correctGetN n
-- +++ OK, passed 100 tests.
-- | Expecting natural numbers
getN :: Integral p => p -> p
getN k =
  if k < 0 then -1 else
  let guess = floor $ sqrt (2 * fromIntegral k + 1/4) - 1/2 in
  let smaller n = if (n + 1) * n `div` 2 > k then smaller (n - 1) else n in
  let bigger n = if (n + 2) * (n + 1) `div` 2 <= k then bigger (n + 1) else n in
  smaller $ bigger guess

enum2D :: Integral p => p -> (p, p)
enum2D k =
  let n = getN k in
  let dif = k - n * (n + 1) `div` 2 in
  (n - dif, dif)

ns :: [Integer]
ns = fmap getN [0..]

-- | Expecting only natural numbers
correctGetN :: Integral p => p -> p
correctGetN k =
  if k < 0 then -1 else findFrom 0 k
  where
    findFrom n k =
      if (n + 1) * n `div` 2 < k + 1 && (n + 2) * (n + 1) `div` 2 >= k + 1 then n
      else findFrom (n + 1) k

-- >>> rptsaExampleCompute 0.7 0.2 0.1 :: Rational
-- 523 % 4700
rptsaExampleCompute :: Fractional a => a -> a -> a -> a
rptsaExampleCompute p1 p2 p3 =
  p3 + (p3^2 * (p1^2 + p2^2)) / (1 - (p1^2 + p2^2))


-- ================================ Roman Number ================================

-- https://leetcode.com/problems/integer-to-roman/description/

-- >>> romanNumber 3
-- "III"
-- >>> romanNumber 5
-- "V"
-- >>> romanNumber 8
-- "VIII"
-- >>> romanNumber 58
-- "LVIII"
-- >>> romanNumber 1994
-- "MCMXCIV"
romanNumber :: Int -> String
romanNumber num =
  printRomanResult $ reverse $ snd $ foldr folder (num, []) romanList
  where
    folder (char, toTest) (rest, res) =
      let (count, newRest) = rest `divMod` toTest in
      (newRest, (count, char) : res)
    printRomanResult lst = do
      ~(count, char) <- lst
      concat $ replicate count char
    romanList :: Integral n => [(String, n)]
    romanList = [
        ("I",  1),
        ("IV", 4),
        ("V",  5),
        ("IX", 9),
        ("X",  10),
        ("XL", 40),
        ("L",  50),
        ("XC", 90),
        ("C",  100),
        ("CD", 400),
        ("D",  500),
        ("CM", 900),
        ("M",  1000)
      ]


-- =================================== Z Algorithm ===================================

-- An implementation of the Z algorithm for string matching


-- given a string `origin` and string `toFind`, find the occurence index in the `origin`
-- the essence of this algorithm is that this is a O(n + m) algorithm

-- >>> zAlgorithm [1] [2, 3]
-- []
-- >>> zAlgorithm "aaaabaaaa" "aab"
-- [2]
zAlgorithm :: Eq a => [a] -> [a] -> [Int]
zAlgorithm origin toFind = reverse $ fetchFromEither $ STT.runSTT $ do
  let lengthOrigin = length origin
  let lengthToFind = length toFind
  let immediateStopping = lengthToFind > lengthOrigin ||
                          null toFind
  -- may terminate the computation at this point
  when immediateStopping $ lift $ Left []
  -- initialise zArrToRun
  zArrToRun <- STT.newSTArray (0, lengthOrigin + lengthToFind) Nothing
  let zArrTemplate = fmap Just toFind ++ [Nothing] ++ fmap Just origin
  forM_ (zip [0..lengthOrigin + lengthToFind] zArrTemplate) $ uncurry $ writeArray zArrToRun
  -- start computation
  leftRef  <- newRef 0
  rightRef <- newRef 0
  zArrItSelf <- STT.newSTArray (0, lengthOrigin + lengthToFind) 0
  ret <- newRef []
  let maxRight = lengthOrigin + lengthToFind
  forM_ [1..lengthOrigin + 1] $ \idx -> do
    let updateLeftFindNewRightAndRecordInfo startLen startRightPos = do
              leftRef <<- idx
              ~(curLength, curRight) <- findNewLength startLen startRightPos
              rightRef <<- curRight
              () <- STT.writeSTArray zArrItSelf idx curLength
              -- collect the information if length OK
              when (lengthToFind == curLength) $ modifyRef ret (idx - lengthToFind - 1 :)

        findNewLength curLength curRight
            | curRight > maxRight = return (curLength, curRight)
            | otherwise = do
              -- use that length = latest idx + 1 that is: the next idx
              initChar  <- STT.readSTArray zArrToRun curLength
              rightChar <- STT.readSTArray zArrToRun curRight
              if initChar /= rightChar then
                return (curLength, curRight - 1)
              else
                findNewLength (curLength + 1) (curRight + 1)

    right <- STT.readSTRef rightRef
    if idx > right then do
      updateLeftFindNewRightAndRecordInfo 0 idx
    else do
      left <- STT.readSTRef leftRef
      let lenToLeft = idx - left
      let lenToRight = right - idx + 1
      lenAtK <- STT.readSTArray zArrItSelf lenToLeft
      if lenAtK < lenToRight then
        STT.writeSTArray zArrItSelf idx lenAtK
      else
        updateLeftFindNewRightAndRecordInfo lenToRight (right + 1)
    -- debugging lines
    -- toRun <- STT.getElems zArrToRun
    -- left <- readRef leftRef
    -- right <- readRef rightRef
    -- let toRun' = fmap (\case { Just a -> show a ++ ", "; Nothing -> "_, " }) toRun
    -- let str = 
    --       "idx: " ++ show idx ++ "; left: " ++ show left ++ "; right: " ++ show right ++
    --       "; the current interval: " ++ if left <= right then "[" ++
    --       concat (take left toRun') ++ " || " ++ 
    --       concat (slice left right toRun') ++ " || " ++ concat (drop (right + 1) toRun') ++ "]" 
    --       else "None"
    -- trace str $ return ()
  -- debugging lines
  -- elems <- STT.getElems zArrItSelf
  -- () <- trace (show elems) $ return ()
  -- finally, return the stored result
  STT.readSTRef ret

-- >>> correctStringMatch [1] [2, 3]
-- []
-- >>> correctStringMatch "aaaabaaaa" "aab"
-- [2]
correctStringMatch :: Eq a => [a] -> [a] -> [Int]
correctStringMatch origin toFind =
  if null toFind then [] else do
  ~(startIdx, toTest) <- zip [0..] $ tails origin
  if not (null toTest) && toFind `isPrefixOf` toTest then return startIdx else []

data TestStringMatch a = TestStringMatch [a] [a] deriving (Eq, Ord, Show)

instance Arbitrary a => Arbitrary (TestStringMatch a) where
  arbitrary :: Arbitrary a => Gen (TestStringMatch a)
  arbitrary = do
    len1 <- arbitrary
    len2 :: Int <- arbitrary
    l1 <- forM [1..len1] $ const arbitrary
    l2 <- forM [1..len2] $ const arbitrary
    -- make sure l2 appears at the real l1 for at least `times` times
    -- as the generation of l1 may contains l2
    times :: Int <- arbitrary
    dividePlace <- fmap sort $ forM [1..if len1 > 0 then times else 0] $ const $ do
      raw <- arbitrary
      return $ raw `mod` len1
    l1' <- (\(_, l1, rest) -> fmap (++ l2) l1 ++ [rest]) <$> foldM baMbFolder (0, [], l1) dividePlace
    return $ TestStringMatch (concat l1') l2
    where
      baMbFolder (curStart, acc, rest) nextPlace =
        let (head, newRest) = splitAt (nextPlace - curStart) rest in
        return (nextPlace, acc ++ [head], newRest)

-- prop> withMaxSuccess 10000 $ \(l :: TestStringMatch Int) -> testZAlgorithm l
-- +++ OK, passed 10000 tests.
testZAlgorithm :: (Show a, Eq a) => TestStringMatch a -> Bool
testZAlgorithm (TestStringMatch origin toFind) =
  -- trace ("testing:\nOrigin:\n" ++ show origin ++ "\nToFind:\n" ++ show toFind) $
  zAlgorithm origin toFind == correctStringMatch origin toFind

-- Check Passed
checkZAlgorithm :: IO ()
checkZAlgorithm = quickCheck $ withMaxSuccess 10000 $ \(l :: TestStringMatch Int) -> testZAlgorithm l

{- | solution to

> a * x^2 + b * x + c = 0

input is `a`, `b` and `c`


>>> sqrtSolution 1 (-2) 1
Just (1.0,1.0)
>>> sqrtSolution (11/16) (-1/2) (1/16)
Just (0.566915270681799,0.1603574565909282)
>>> sqrtSolution 1 1 1
Nothing
>>> sqrtSolution 1 0 (-1)
Just (1.0,-1.0)
-}
sqrtSolution :: (Ord b, Floating b) => b -> b -> b -> Maybe (b, b)
sqrtSolution a b c = do
  let judge = b^2 - 4 * a * c
  guard (judge >= 0)
  let sq = sqrt judge
  return ((-b + sq)/(2 * a), (-b - sq)/(2 * a))
