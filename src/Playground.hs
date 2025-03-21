{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
-- {-# LANGUAGE FlexibleContexts #-}

module Playground where

import qualified Data.List as List
import Data.List.Split
import qualified GHC.List as List
import qualified Data.Maybe as Maybe
import qualified GHC.Maybe as Maybe
import Utils
import Test.QuickCheck (quickCheck, Arbitrary (arbitrary))
import Debug.Trace (trace, traceShow)
import Data.Maybe (listToMaybe)
import qualified Data.Set as Set
import Control.Monad
import Data.List (intercalate, findIndex)
import Data.Char (isDigit)
import Text.Read (readMaybe)
import qualified Test.QuickCheck.Gen
import WorkingTest (lst)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Cont (MonadCont(..))
import Control.Monad.Trans.Cont hiding (callCC)
import qualified Control.Monad.Logic as L
import Control.Monad.Reader.Class (MonadReader (..))
import qualified DataStructure.RBTree as RBT

-- | Toy to find the first letter that is NOT mentioned in the given word
firstLetterNotIn :: String -> Maybe Char
firstLetterNotIn word =
  Maybe.listToMaybe [ c | c <- ['m'..'z'], c `notElem` word ]

-- | To print out the actual testing data
seeQuickCheckNumbers :: IO ()
seeQuickCheckNumbers =
  -- use " |   " to mark those generated by the current one
  -- Because the testing will auto generate some information
  quickCheck $ \(int :: Integer) -> trace (show int ++ " |   ") True

testHigherRank :: Num m => (forall a1. a1 -> a1) -> (m, [Char])
testHigherRank (f :: forall m. m -> m) = (f 1, f "m")

moreHigherRank :: (forall b. (forall m. m -> m) -> b) -> (forall b. b -> b)
moreHigherRank f = f id

-- | This is to test that one may customise the execution while providing m general implementation
class MyShow m where
  -- Default implementation can exist ALONG WITH general implementation
  myShow :: m -> Int
  myShow = const 0

-- | This is the general implementation
instance (Show m) => MyShow m where
  myShow :: Show m => m -> Int
  myShow m = maybe 0 ((+1) . fromEnum) (listToMaybe $ show m)

instance MyShow Int where
  myShow :: Int -> Int
  myShow = id

instance (Enum m) => MyShow [m] where
  myShow :: [m] -> Int
  myShow lst = maybe 0 ((+1) . fromEnum) (listToMaybe lst)

data MyType = MyType

instance MyShow MyType where
  myShow :: MyType -> Int
  myShow = const 1

justShow :: MyShow m => m -> Int
justShow = myShow

-- NO -- This is also not viable, as Mappable requires additional target
-- -- | This seems to be general enough, however, one will have to declare the stuff
-- class Mappable m b

-- mapBothMap :: (Mappable m b, Mappable c d) => 
--   (forall m b. (Mappable m b) => m -> b) -> (m, c) -> (b, d)
-- mapBothMap f (m, c) = (f m, f c)

-- instance (Show m) => Mappable m String

-- showBoth' :: (Show m, Show b) => (m, b) -> (String, String)
-- showBoth' = mapBothMap (show :: forall m. (Show m, Mappable m String) => m -> String)

-- | Some test on the BothMap -- Show m is an `evidence` with default proof (during `instance Show m`)
--   So, one must provide also such evidence requirement so to allow the following function to be valid
--   In general, it means there is NOT m general function that can accomplish the task
myBothMap :: (forall m. Show m => m -> b) -> forall m c. (Show m, Show c) => (m, c) -> (b, b)
myBothMap f (m, c) = (f m, f c)

showBoth :: (Show m, Show b) => (m, b) -> (String, String)
showBoth = myBothMap show

-- | The example of very flexible definition of constraints
class MyClass m where
  display :: m -> String

-- instance Show m => MyClass [m] where
--   display :: Show m => [m] -> String
--   display xs = "List: " ++ show xs

instance MyClass String where
  display :: String -> String
  display = id

-- >>> foo 'm'
-- "aa"
-- | Although there is NO `MyClass` for m single element type `m`, it is OK to put them in list
foo :: (MyClass [m]) => m -> String
foo x = display [x, x]

-- | Test Non-General GADTs
--   So the possible forms of the types are limited
data NonGeneral m where
  NGInt :: Int -> NonGeneral Int
  NGBool :: NonGeneral Bool

useNonGeneral :: NonGeneral m -> Int
useNonGeneral = \case
  NGInt idx -> idx
  NGBool    -> 0

data Expr m where
  I   :: Int  -> Expr Int
  B   :: Bool -> Expr Bool
  Add :: Expr Int -> Expr Int -> Expr Int
  Eq  :: Expr Int -> Expr Int -> Expr Bool

eval :: Expr m -> m
eval (I n)       = n
eval (B b)       = b
eval (Add e1 e2) = eval e1 + eval e2
eval (Eq e1 e2)  = eval e1 == eval e2


-- =========================== Play with Argument-Analysis-related Stuff ===========================

-- >>> caseView "-d"
-- "debug"
caseView :: [Char] -> [Char]
caseView x =
  case x of
    (view -> "d") -> "debug"
    (view -> "id") -> "internal debug"
    _otherwise -> "unknown"
  where
    view x
      | x `elem` [ "-d", "-debug" ] = "d"
      | x `elem` [ "-inner_debug", "-inD" ] = "id"
      | otherwise = "m"

-- | `prob` is m number type
data Dist prob ty where
  Dist :: (Fractional prob) => [(prob, ty)] -> Dist prob ty

class MarkovChain mc st p | mc -> st, mc -> p where
  states :: mc -> Set.Set st
  getDist :: mc -> st -> Dist p st

class Cofunctor f where
  cofmap :: (b -> m) -> f m -> f b

newtype Cow m = Cow (m -> Bool)

instance Cofunctor Cow where
  cofmap :: (b -> m) -> Cow m -> Cow b
  cofmap f (Cow af) = Cow $ \m -> af $ f m

-- >>> cFunc 11 0
-- 1
-- >>> cFunc 3 1
-- 3
-- >>> cFunc 11 1
-- 11
-- >>> cFunc 11 2
-- 55
-- >>> cFunc 11 3
-- 165
combination :: Integral p => p -> p -> p
combination n r
  | n <= 0    = error "Invalid `n`."
  | r < 0     = error "Invalid `r`."
  | n < r     = error "`n` < `r`."
  | r == 0    = 1
  | otherwise = product [n - r + 1..n] `div` product [1..r]

-- >>> arrangement 11 2
-- 110
arrangement :: (Ord p, Num p, Enum p) => p -> p -> p
arrangement n r
  | n <= 0    = error "Invalid `n`."
  | r < 0     = error "Invalid `r`."
  | n < r     = error "`n` < `r`."
  | r == 0    = 1
  | otherwise = product [n - r + 1..n]

rearrangeTex :: String -> String
rearrangeTex str =
  let content = str in
  let paragraphs = splitOn "\n\n" content in
  let singleLineParagraphs = map (unwords . words) paragraphs in
  concatStr "\n\n" singleLineParagraphs

rearrangeTexFile :: String -> IO ()
rearrangeTexFile path = do
  str <- readFile path
  let res = rearrangeTex str
  writeFile path res

fixPointCondition :: IO ()
fixPointCondition = do
  foldM_ folderM (0.67, 0.71) [0..10]
  where
    folderM (x, y) idx = do
      let p@(x', y') = run x y
      putStrLn $ unwords
        [ show idx
        , ":"
        , show (x, y)
        , "==>"
        , quoteWith "()" $ unwords
          [ show x'
          , printCmp x' x
          , ","
          , show y'
          , printCmp y' y ] ]
      return p
    run x y = (1/2 * (1 + x * y^2), 1/3 * (1 + x + y))
    printCmp x' x = if x' > x then "^" else "v"


-- 进一步泛化 test
compute :: [Char] -> IO ()
compute str = putStrLn $ intercalate "、" [  x : "字旁" | x <- str ]

-- 只有通过 putStrLn 才能打印出 UTF-8 编码文字
test :: IO ()
test = putStrLn $ intercalate "、" [  x : "字旁" | x <- "口日目月山石弓身" ]


genYn :: Int -> IO ()
genYn n =
  forM_ [0..n-1] $ \i ->
    putStrLn $ "Y" ++ show n ++ " -(1/" ++ show n ++ ")-> " ++ unwords (replicate i "Young") ++ "."


-- | genXn "Young4": Y4 -(1/4)-> {Young}^i.  -- i \in [0..3]
genXn :: String -> IO ()
genXn input =
  let (abbr, name, n) = unwrap $ parseInput input in
  mapM_ putStrLn $ genXn abbr name n
  where
    parseInput :: String -> Maybe (String, String, Int)
    parseInput input = case break isDigit input of
      (name, numStr) -> do
          num <- readMaybe numStr
          let abbr = take 1 name
          return (abbr, name, num)
    genXn abbr name n =
      forM [0..n-1] $ \i ->
        abbr ++ show n ++ " -(1/" ++ show n ++ ")-> " ++ unwords (replicate i name) ++ "."


(-|) :: [Char] -> [Char] -> [Char]
name -| rule = name ++ " -(" ++ rule

infixl 1 -|

(|->) :: [Char] -> [Char] -> [Char]
prob |-> rule = prob ++ ")-> " ++ rule ++ "."

infixl 2 |->

escapeNStr :: Int -> [String]
escapeNStr m =
  flip concatMap [0..m-1] $ \n ->
    let name = "F" ++ show n
        nextName = "F" ++ show ((n + 1) `mod` m) in
    [ name -| show (n+1) ++ "/" ++ show (n+2) |-> unwords [ nextName, nextName ]
    , name -| "1/" ++ show (n+2) |-> "" ]

escapeN :: Int -> IO ()
escapeN m =
  mapM_ putStrLn $
  flip concatMap [0..m-1] $ \n ->
    let name = "F" ++ show n
        nextName = "F" ++ show ((n + 1) `mod` m) in
    [ name -| show (n+1) ++ "/" ++ show (n+2) |-> unwords [ nextName, nextName ]
    , name -| "1/" ++ show (n+2) |-> "" ]


modN :: Int -> IO ()
modN n =
  mapM_ putStrLn $
  flip concatMap [0..n-1] $ \i ->
    {-
      Fn -> {FPn}*
      FPn -(2/3)-> F{n-1}
      FPn -(1/3)-> F{n+1%N}
    -}
    let fn = "F" ++ show i
        fpn = "FP" ++ show i
        fn_1 = "F" ++ show (i - 1)
        fnP1 = "F" ++ show ((i + 1) `mod` n)
    in
    (fn -| "1" |-> unwords (replicate i fpn)) :
    concat [ [ fpn -| "2/3" |-> fn_1
           , fpn -| "1/3" |-> fnP1 ] | i > 0 ]


-- >>> kaigeJan2
-- 1 % 6
kaigeJan2 :: Rational
kaigeJan2 = fromIntegral kaigeJan2Match / fromIntegral (length $ arrange [0..4])
  where
  kaigeJan2Match = length [ 1 | lst <- arrange [0..4], match lst == 2 ]
  match lst = length [ 1 | (i, x) <- zip [0..] lst, i == x ]

data Pred m = PAtom m | PAnd (Pred m) (Pred m) | POr (Pred m) (Pred m)

-- `d` represents the expansion of definitions
newtype LabelInputPair m d = LabelInputPair (m, [d])

mixUp :: Pred (LabelInputPair m d) -> LabelInputPair (Pred m) (Pred d)
mixUp (PAtom (LabelInputPair (m, dlst))) = LabelInputPair (PAtom m, fmap PAtom dlst)
mixUp (PAnd pr pr') =
  let (LabelInputPair (la, lDlst)) = mixUp pr
      (LabelInputPair (ra, rDlst)) = mixUp pr' in
  LabelInputPair (PAnd la ra, uncurry PAnd <$> zip lDlst rDlst)
mixUp (POr pr pr') =
  let (LabelInputPair (la, lDlst)) = mixUp pr
      (LabelInputPair (ra, rDlst)) = mixUp pr' in
  LabelInputPair (POr la ra, uncurry POr <$> zip lDlst rDlst)


-- >>> groupAbove (> 3) [1, 5, 6, 2, 0, -1, 7, 8, 1, 9]
-- [[5,6,2],[7,8,1],[9]]
groupAbove :: (m -> Bool) -> [m] -> [[m]]
groupAbove = groupA []
  where
    groupA :: [m] -> (m -> Bool) -> [m] -> [[m]]
    groupA acc _ []
      | null acc  = []
      | otherwise = [acc]
    groupA acc itHolds (x:xs)
      | itHolds x = groupA (acc ++ [x]) itHolds xs
      | null acc  = groupA [] itHolds xs
      | otherwise = (acc ++ [x]) : groupA [] itHolds xs

-- prop> \(MyPair x y) -> x >= 0 && y <= 0
-- +++ OK, passed 100 tests.
data MyPair = MyPair Int Int
  deriving (Show)

instance Arbitrary MyPair where
  arbitrary :: Test.QuickCheck.Gen.Gen MyPair
  arbitrary = do
    x <- arbNonNeg
    y <- arbNonPos
    return $ MyPair x y
    where
      arbNonNeg = do
        x <- arbitrary
        if x < 0 then arbNonNeg
        else return x
      arbNonPos = do
        y <- arbitrary
        if y > 0 then arbNonPos
        else return y

testMyPair :: IO ()
testMyPair = quickCheck $ \(MyPair x y) -> x >= 0 && y <= 0

-- >>> differentKinds 3 2
-- [[[1,2,3],[]],[[2,3],[1]],[[1,3],[2]],[[3],[1,2]],[[1,2],[3]],[[2],[1,3]],[[1],[2,3]],[[],[1,2,3]]]
differentKinds :: (Ord n, Num n, Num m, Enum m) => m -> n -> [[[m]]]
differentKinds m n =
  recDo [1..m] n
  where
    recDo lst n
      | n <= 0 = []
      | n == 1 = [[lst]]
      | otherwise = do
        (this, that) <- enumSets lst
        those <- recDo that (n - 1)
        return $ this : those
    enumSets :: [a] -> [([a], [a])]
    enumSets [] = [([],[])]
    enumSets (hd:lst) = do
      (this, that) <- enumSets lst
      [ (hd:this, that), (this, hd:that) ]


-- | Enumerate all the different sets of `m` different numbers grouped into `n` sets
--   The return values are all list but are guaranteed to be proper sets
-- 
-- >>> diffSets 3 2
-- [[[3,1],[2]],[[1],[3,2]],[[3],[1,2]]]
-- 
-- >>> diffSets 4 3
-- [[[4,1],[2],[3]],[[1],[4,2],[3]],[[1],[2],[4,3]],[[4],[3,1],[2]],[[4],[1],[3,2]],[[4],[3],[1,2]]]
diffSets :: (Ord t, Num t, Enum t) => t -> t -> [[[t]]]
diffSets m n
  | n <= 0 || n > m = []
  | n == 1 = [[[1..m]]]
  | n == m = [fmap (:[]) [1..n]]
  | otherwise = addToSet m n ++ emptySet m n
  where
    addToSet m n = do
      sets <- diffSets (m - 1) n
      -- assign `m` to each of them
      recAdd m sets
    emptySet m n = do
      sets <- diffSets (m - 1) (n - 1)
      return $ [m] : sets
    recAdd _ [] = eIMPOSSIBLE
    recAdd m [x] = [[m:x]]
    recAdd m (hd:lst) =
      let rest = do lst <- recAdd m lst; return (hd:lst) in
      ((m:hd):lst) : rest

testShift :: IO ()
testShift = evalContT $ do
  i <- resetT $ do
    i <- tryCallShift
    return $ i + 1
  liftIO $ putStrLn $ "Ending with return " ++ show i
  where
    tryCallShift = do
      shiftT $ \rest -> do
        liftIO $ putStrLn "start shifting"
        i <- lift $ rest 1
        liftIO $ putStrLn "end shifting"
        return i

testContT :: IO ()
testContT = do
  res <- evalContT $ do
    res <- callCC $ \ret -> do
      liftIO $ putStrLn "Start"
      -- resetT $ do
      shiftT $ \rest -> do
        liftIO $ putStrLn "Start shifting"
        res <- lift $ rest ()
        -- ret $ res + 1
        liftIO $ putStrLn $ "End shifting, obtained result: " ++ show res
        return 100
        -- ret 1000
      ret 1
      liftIO $ putStrLn "Normal End"
      return 10
    liftIO $ putStrLn $ "Outside callCC: " ++ show res
    return res
  putStrLn $ "Final Result: " ++ show res

testContT2 :: IO ()
testContT2 = do
  res <- evalContT $ do
    res <- callCC $ \(ret :: Int -> ContT Int IO ()) -> do
      resetT $ do ret 100; liftIO $ putStrLn "In reset"; return 10
      ret 1
      return 0
    liftIO $ putStrLn $ "Outside callCC result: " ++ show res
    return $ res + 1
  putStrLn $ "Final Result: " ++ show res

infixl 8 *.

-- prop> \(n :: Int) -> length ("a" *. n) == max n 0 
-- +++ OK, passed 100 tests.
(*.) :: (Num t, Ord t) => [a] -> t -> [a]
lst *. n
  | n <= 0 = []
  | n == 1 = lst
  | otherwise = lst ++ (lst *. (n - 1))

-- >>> producer 5 1
producer :: (Eq a, Num a, Show a) => a -> a -> String
producer max i =
  let this = i in
  let that = if i - 1 == 0 then max else i - 1 in
  genStr this that
  where
    indent = "    "
    genStr this that = concatStr "\n"
      [ "if (p" ++ show this ++ " == op" ++ show that ++ ") {"
      , indent ++ "prob {"
      , indent *. 2 ++ "0.5 : p" ++ show this ++ " = 0;"
      , indent *. 2 ++ "0.5 : p" ++ show this ++ " = 1;"
      , indent ++ "}"
      , "}"
      , "else {"
      , indent ++ "p" ++ show this ++ " = op" ++ show that ++ ";"
      , "}" ]

printProducer :: IO ()
printProducer = forM_ [1..5] $ putStrLn . producer 5
