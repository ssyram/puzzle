{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}
module SimpleAutomata where

import Utils
import Control.Monad.State.Strict
import Data.Maybe
import Data.List
import Data.Set as Set hiding (map, null, foldl)
import Data.Map.Lazy as Map (Map, empty, insert, keys, (!?))
import Test.QuickCheck
import Debug.Trace
import Data.Function

-- A file for simple definition of automata

data Automata s l = Automata {
  startStates :: [s],
  finalStates :: [s],
  states :: [s],
  transition :: s -> Maybe l -> [s],
  alphabet :: [l]
}

-- instance Arbitrary (Automata Integer Char) where
--   arbitrary = return exampleFSA

instance (Arbitrary n, Arbitrary m, Ord n, Ord m, Show n) => Arbitrary (Automata n m) where
  arbitrary = do
    -- !(sts :: [n]) <- untilM (\x -> do { c <- x; trace ("obtained c = " ++ show c) $ return $ not $ null c}) 
    --   (const arbitrary) arbitrary
    -- !(als :: [m]) <- untilM (\x -> not . null <$> x) (const arbitrary) arbitrary
    sts <- arbitrary1
    als <- arbitrary1
    let !states = unique sts
    let !alphabet = unique als
    -- !() <- trace ("Length of sts: " ++ show (length sts) ++ "; length of als: " ++ show (length als)) $ return ()
    !startStates <- getArbitrarySubList states False
    !finalStates <- getArbitrarySubList states False
    transitionKernel <- foldM (\m (s, l) -> do lst <- getArbitrarySubList states False; return $ Map.insert (s, l) lst m)
      Map.empty $ [(s, l) | s <- states, l <- Nothing : map Just alphabet]
    let transition = \s l -> fromMaybe [] (transitionKernel Map.!? (s, l))
    return $ Automata startStates finalStates states transition alphabet
    where
      getArbitrarySubList states notNull = do
        ssInit <- forM states $ \st -> do
          (select :: Bool) <- arbitrary
          if select then return $ Just st else return Nothing
        let ssTmp = [x | st <- ssInit, isJust st, let Just x = st]
        return $ if notNull && null ssTmp then [head states] else ssTmp

normalise :: (Ord s, Ord a) => Automata s a -> Automata s a
normalise at =
  Automata {
    startStates = unique $ startStates at,
    finalStates = unique $ finalStates at,
    states = unique $ states at,
    transition = transition at,
    alphabet = unique $ alphabet at
  }

instance (Show s, Show g) => Show (Automata s g) where
  show fsa =
    "States = " ++ show (states fsa) ++ "\n" ++
    "Starting States = " ++ show (startStates fsa) ++ "\n" ++
    "Acc States = " ++ show (finalStates fsa) ++ "\n" ++
    "Stack Symbols = " ++ show (alphabet fsa) ++ "\n" ++
    "Transisions = {\n" ++ printTrans fsa ++ "}"
    where
      printTrans fsa =
        let st = states fsa in
        let gs = map Just (alphabet fsa) ++ [Nothing] in
        do {
          s <- st;
          g <- gs;
          let res = transition fsa s g in
          if null res then ""
          else "  " ++ show s ++ ", " ++ maybe "\\epsilon" show g ++ " |-> " ++ show res ++ "\n"
        }

generateAutomata :: [s] -> [s] -> [s] -> (s -> Maybe l -> [s]) -> [l] -> Automata s l
generateAutomata = Automata

isDeterministic :: Automata a l -> Bool
isDeterministic at =
  -- there should be no epsilon transition
  and [ null (transition at st Nothing) | st <- states at ] &&
  -- for non-epsilon transitions, there should be at most one target
  and [ length (transition at st label) <= 1 | st <- states at, label <- map Just (alphabet at) ]

epsilonClosure :: Eq a => Automata a l -> a -> [a]
epsilonClosure at s =
  inner [s] [s]
  where
    inner [] lst = lst
    inner (h:rst) res =
      let toExplores = [ s | s <- transition at h Nothing, s `notElem` res, s `notElem` rst] in
      inner (toExplores ++ rst) (h:res)
-- >>> isDeterministic exampleFSA
-- False
-- >>> isDeterministic $ toDeterministic exampleFSA
-- True
exampleFSA :: Automata Integer Char
exampleFSA = Automata {
  states = [0..2],
  startStates = [0],
  finalStates = [2],
  alphabet = ['a'..'c'],
  transition = trans
}
  where
    trans 0 (Just 'a') = [1, 2]
    trans 0 Nothing = [1]
    trans 1 (Just 'b') = [2]
    trans 2 (Just 'c') = [1]
    trans 2 Nothing = [0]
    trans _ _ = []

invalidAutomata :: Automata s a -> Bool
invalidAutomata at =
  null (states at) &&
  null (startStates at) &&
  null (alphabet at)

emptyAutomata :: Automata s l
emptyAutomata = Automata [] [] [] (\_ _ -> []) []

{-| Convert the given automaton to its deterministic form

prop> \(at :: Automata Int Int) -> isDeterministic $ toDeterministic at
+++ OK, passed 100 tests.
-}
toDeterministic :: (Ord a, Ord l) => Automata a l -> Automata (Set a) l
toDeterministic at =
  if invalidAutomata at then emptyAutomata else
  getResult $
  (`execState` initVal) $ do
    while (not . null . getTodoList) $ do
      !(newSt :: Set a) <- getNextTodo
      moveToNextTodo
      forM_ (alphabet at) $ \label -> do
        let !nextSt = computeNextState newSt label
        addTransition newSt label nextSt
        tryAddTodo nextSt
  where
    getResult (_, transMap, _) =
      let (keys, alphabets) = unzip $ Map.keys transMap in
      let fs = Set.fromList $ finalStates at in
      Automata {
        startStates = [ Set.fromList $ startStates at ],
        finalStates = [st | st <- keys, not $ null $ Set.toList $ fs `Set.intersection` st],
        states = keys,
        transition = \s l -> case l of { Just l -> Data.Maybe.maybeToList $ transMap Map.!? (s, l); _ -> [] },
        alphabet = alphabets
      }
    -- data structure: (todoList, transitionMap, exploredSt)
    initVal = ([Set.fromList $ do {st <- startStates at; epsilonClosure at st}], Map.empty, Set.empty)
    moveToNextTodo = do
      (~(_:a), b, c) <- get
      put (a, b, c)
    getTodoList (x, b, c) = x
    getNextTodo = do { (~(h:_), _, _) <- get; return h }
    -- addTransition :: s -> l -> s -> State (a, Map (s, l) s, b) ()
    addTransition st l st' = modify $ \(lst, m, a) -> (lst, Map.insert (st, l) st' m, a)
    -- tryAddTodo :: s -> State ([s], b, Set s) ()
    tryAddTodo newSt = do
      (!l, !m, !exploredSt) <- get
      when (newSt `Set.notMember` exploredSt) $ put (l++[newSt], m, Set.insert newSt exploredSt)
    computeNextState setOfStates label =
      Set.fromList $ do
        !st <- Set.toList setOfStates
        !nst <- transition at st $ Just label
        epsilonClosure at nst

normaliseAutomata :: (Ord s, Ord l) => Automata s l -> Automata Integer Integer
normaliseAutomata at =
  let stateMap = getMap $ states at in
  let alMap = getMap $ alphabet at in
  Automata {
    states = [0..toInteger $ length (states at) - 1],
    startStates = subsetMap startStates stateMap,
    finalStates = subsetMap finalStates stateMap,
    alphabet = [0..toInteger $ length (alphabet at) - 1],
    transition = 
      let transitionKernel = getTransitionMap stateMap alMap in
      \k l -> fromMaybe [] $ transitionKernel !? (k, l)
  }
  where
    getMap st = fst $ foldl (\(m, c) st -> (Map.insert st c m, toInteger $ c + 1)) (Map.empty, toInteger 0) st
    subsetMap states stateMap = [fromJust $ stateMap !? x | x <- states at]
    getTransitionMap stateMap alMap =
      ($ [(s, l) | s <- states at, l <- Nothing : map Just (alphabet at)]) $
      ($ Map.empty) $
      foldl $ \m (s, l) ->
        let resSt = transition at s l in
        let label = fmap (\x -> fromJust $ alMap !? x) l in
        Map.insert (fromJust $ stateMap !? s, label) [fromJust $ stateMap !? x | x <- resSt] m

testDeterministic :: IO ()
testDeterministic = quickCheck $ \(at :: Automata Int Int) -> isDeterministic $ toDeterministic at
