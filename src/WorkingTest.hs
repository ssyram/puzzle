{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
module WorkingTest where

import Utils
import Test.QuickCheck
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List
import Data.Either

-- The file to record some working tests

{- | for each para, there are several candidates, enumerate all possible paras

prop> testEnumStuff
-}
enumStuff :: [[a]] -> [[a]]
enumStuff [] = []
enumStuff [col] = do x <- col; return [x]
enumStuff (col : rst) = do
  x <- col
  stuff <- enumStuff rst
  return $ x : stuff

packParas :: ([a] -> b) -> [[a]] -> [b]
packParas pack stuff = do
  paras <- enumStuff stuff
  return $ pack paras

testEnumStuff :: [[Int]] -> Bool
testEnumStuff stuff =
  let lenStuff = length stuff in
  all (lenEq lenStuff) $ enumStuff stuff


-- | compute one step of the `pre` function for a pPDA set
-- Note that this function will preserve also the original function
preOneStep :: (Foldable t1, Ord a2, Ord b) =>
     t1 ((t2, b), (t2, [b]))
  -> Map.Map (a2, b) (Set.Set a2)
  -> (t2 -> a2)
  -> Map.Map (a2, b) (Set.Set a2)
preOneStep pdaRules initNfa stateTrans =
  flip (`foldl` initNfa) pdaRules $ \nfa ((q, s), (q', ss)) ->
    flip (`foldl` nfa) (runNfa initNfa (stateTrans q') ss) $ \nfa ar ->
      addNfaRule nfa (stateTrans q, s, ar)

maybeSetToList :: Maybe (Set.Set a) -> [a]
maybeSetToList Nothing    = []
maybeSetToList (Just set) = Set.toList set

runNfa :: (Ord t, Ord b) => Map.Map (t, b) (Set.Set t) -> t -> [b] -> [t]
runNfa nfa q [] = return q
runNfa nfa q (x:xs) = do
  nq <- maybeSetToList $ nfa Map.!? (q, x)
  runNfa nfa nq xs

addNfaRule :: (Ord a1, Ord b, Ord a2) =>
  Map.Map (a1, b) (Set.Set a2) -> (a1, b, a2) -> Map.Map (a1, b) (Set.Set a2)
addNfaRule nfa (q, s, ar) =
  Map.insertWith Set.union (q, s) (Set.fromList [ar]) nfa

-- | compute the `pre*` of the given pPDA pdaRules and initial NFA
preStar pdaRules initNfa stateTrans =
  let nfa = preOneStep pdaRules initNfa stateTrans in
  if nfa == initNfa then nfa else preStar pdaRules nfa stateTrans

-- | the `newStateTrans` will transform the states into newly construct states
-- in order to perform `pre` without preserving the original configurations, one will need to
-- create new set of initial states in order not make the original one interfere the new one here
preOneStepNonPreserving :: (Foldable t1, Ord a2, Ord b) =>
     t1 ((t2, b), (t3, [b]))
  -> Map.Map (a2, b) (Set.Set a2)
  -> (t3 -> a2)
  -> (t2 -> a2)
  -> Map.Map (a2, b) (Set.Set a2)
preOneStepNonPreserving pdaRules initNfa oldStateTrans newStateTrans =
  flip (`foldl` initNfa) pdaRules $ \nfa ((q, s), (q', ss)) ->
    flip (`foldl` nfa) (runNfa initNfa (oldStateTrans q') ss) $ \nfa ar ->
      addNfaRule nfa (newStateTrans q, s, ar)

prePlus pdaRules initNfa oldStateTrans newStateTrans =
  let nfa = preOneStepNonPreserving pdaRules initNfa oldStateTrans newStateTrans in
  -- here, use the new one to make all operations be performed on the new initial states
  preStar pdaRules initNfa newStateTrans

class (Ord t) => InfiniteIncreasible t where
  incr :: t -> t
instance InfiniteIncreasible Int where
  incr = (+1)
instance InfiniteIncreasible Integer where
  incr = (+1)
-- | an example function for generating `newStateTrans`
exampleGenNewStateTrans :: (InfiniteIncreasible a, Ord k) =>
  [((k, b1), (k, b2))] -> (k -> a) -> k -> a
exampleGenNewStateTrans pdaRules oldStateTrans =
  let qs = collectAllQs pdaRules in
  let maxVal = maximum $ fmap oldStateTrans qs in
  let map = snd $ foldl (\(v, map) q -> (incr v, Map.insert q v map)) (incr maxVal, Map.empty) qs in
  (map Map.!)

collectAllQs :: Ord a => [((a, b1), (a, b2))] -> [a]
collectAllQs pdaRules =
  Set.toList $ Set.fromList $ do ((q, _), (q', _)) <- pdaRules; [q, q']

collectAllGammas :: Ord a1 => [((a2, a1), (a3, [a1]))] -> [a1]
collectAllGammas pdaRules =
  Set.toList $ Set.fromList $ do ((_, x), (_, xs)) <- pdaRules; x : xs

data BuchiAutomaton d s = BuchiAutomaton {
  buchiInits :: Set.Set d,
  buchiRules :: Map.Map (d, s) d,
  buchiAccQs :: Set.Set d
}

productRules :: Eq b1 =>
     [((a1, b1), (a2, b2))]
  -> BuchiAutomaton b3 b1
  -> [(((a1, b3), b1), ((a2, b3), b2))]
productRules pdaRules buchiAut =
  [
    (((q, d), x), ((p, b), xs))
    |
    ((q, x), (p, xs)) <- pdaRules,
    ((d, x'), b) <- Map.toList $ buchiRules buchiAut,
    x == x'
  ]

isSet :: Eq a => [a] -> Bool
isSet []       = True
isSet (x : xs) = x `notElem` xs && isSet xs



-- help function to test something
calculateQGamma q gamma = (q + gamma + 1)^(q + gamma + 1) - q^(2 * gamma)
-- >>> fmap (\(x, y, _) -> (x, y)) lst
lst :: [(Integer, Integer, Integer)]
lst =
  [
  (q, gamma, res)
  |
  q <- [1..100],
  gamma <- [1..100],
  let res = calculateQGamma q gamma,
  res < 0
  ]


type NonTerminal = String
type Variable = String

-- | generate a new variables that is distinct from the given ones
newVariable :: [Variable] -> Variable
newVariable varList = undefined

data LambdaCFG c =
    LCFGLambda Variable (LambdaCFG c)
  | LCFGApp (LambdaCFG c) (LambdaCFG c)
  | LCFGChar c
  | LCFGVar Variable
  | LCFGNonTerminal NonTerminal

newtype CVString c = CVString [Either Variable c]

data MCFGRule c = MCFGRule { lhs :: [CVString c], rhs :: [(NonTerminal, [Variable])] }

data MCFG c = MCFG { rules :: [(NonTerminal, MCFGRule c)], startingSymbol :: NonTerminal }

ruleDimension :: MCFGRule c -> Int
ruleDimension (MCFGRule lhs rhs) =
  max (length lhs) $ maximum $ fmap (length . snd) rhs

mcfgDimension :: MCFG c -> Int
mcfgDimension mcfg = maximum $ ruleDimension . snd <$> rules mcfg

ruleRank :: MCFGRule c -> Int
ruleRank (MCFGRule _ rhs) = length rhs

mcfgRank :: MCFG c -> Int
mcfgRank mcfg = maximum $ ruleRank . snd <$> rules mcfg

cvStringToLambdaCFG :: CVString c -> LambdaCFG c
cvStringToLambdaCFG (CVString cvs) =
  let varZ = newVariable [ v | e <- cvs, isLeft e, let (Left v) = e ] in
  fmap cOrV cvs
  |> foldr (flip LCFGApp) (LCFGVar varZ)
  |> LCFGLambda varZ
  where
    cOrV (Left var) = LCFGVar var
    cOrV (Right c) = LCFGChar c

ruleToLambdaCFG :: MCFGRule c -> LambdaCFG c
ruleToLambdaCFG (MCFGRule lhs rhs) =
  let varT = newVariable [ e | e <- concatMap snd rhs ] in
  -- convert LHS first
  fmap cvStringToLambdaCFG lhs  -- [LambdaCFG c]
  |> foldl LCFGApp (LCFGVar varT)  -- LambdaCFG c
  |> flip (foldl foldFunc) rhs
  |> LCFGLambda varT
  where
    foldFunc :: LambdaCFG c -> (NonTerminal, [Variable]) -> LambdaCFG c
    foldFunc internalTerm (nt, vars) =
      LCFGApp (LCFGNonTerminal nt) $ foldr LCFGLambda internalTerm vars

mcfgToLambdaCFG :: MCFG c -> (NonTerminal, [(NonTerminal, LambdaCFG c)])
mcfgToLambdaCFG mcfg = (startingSymbol mcfg, sndMap ruleToLambdaCFG <$> rules mcfg)

