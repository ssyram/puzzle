{-# LANGUAGE FlexibleInstances #-}
module SimpleRegularLanguage where

import Data.Functor
import Control.Monad
import Control.Monad.State.Strict
import Data.Maybe
import Data.Function
import Debug.Trace
import Data.List as List
import Utils
import Control.Monad.ST
import Data.STRef
import Data.Array.ST

-- >>> execState testWhile 1
-- 100
testWhile :: State Int ()
testWhile = do
  whileM (get <&> (< 100)) $ do
    n <- get
    put $ n + 1

-- >>> testFor
-- 20
testFor :: Integer
testFor = execState (do {
    forM_ [1, 2, 3, 4] (\i -> do { n <- get; put $ n + i })
  }) 10

data AutomataInfo = AutomataInfo {
  nodeCount :: Integer,
  curNode :: Integer,
  transition :: Integer -> Char -> Maybe Integer,
  acceptingNodes :: [Integer],
  throughNodes :: [Integer],
  recentEdge :: Maybe Char
}

{-| This is the state to compute DFA out of a string, need to execute this state with suitable initial state

From this angle, this function is just an auxiliary function.

BUG DETECTED BUT NOT FIXED: although the key is to construct DFA, but rules like "a*a" will create NFA itself
For this special rule, the latter one will erase the former rule, so a will just make transition to next
-}
automataParserState :: String -> State AutomataInfo ()
automataParserState str =
  case str of
    h:rst -> do {
      case h of {
        '*' -> do {
          node <- getCurNode;
          edge <- getRecentEdge;
          -- A unit "if" without else
          when (isNothing edge) $ error "Not Valid Input Pattern -- * at start or multiple *";
          setRecentEdge Nothing;
          addSelfRing node $ fromJust edge
        };
        x   -> do {
          throughNodes <- getThroughNodes;
          newNode <- createNewNode;
          -- put all through nodes link with the edge to current new node
          -- trace ("Through nodes" ++ show throughNodes) $
          forM_ throughNodes $ \node -> addNewEdge node x newNode;
          recentEdge <- getRecentEdge;
          curNode <- getCurNode;
          -- Debug: the start node is not cleared if it is from start
          --        if the current node is the start node, it means one should clear it
          when (isJust recentEdge || curNode == 0) clearThroughNodes;
          setCurNode newNode;
          setRecentEdge $ Just x
        }
      };
      addCurNodeToThroughNodes;
      automataParserState rst
    }
    [] -> do
      recentEdge <- getRecentEdge
      -- Debug: if the recently added edge is not '*', then the final nodes should only be the curNode
      when (isJust recentEdge) $ do { clearThroughNodes; addCurNodeToThroughNodes }
      setFinalNodes =<< getThroughNodes
  where
    getCurNode :: State AutomataInfo Integer
    getCurNode = curNode <$> get
    getRecentEdge = recentEdge <$> get
    getThroughNodes = throughNodes <$> get
    setRecentEdge :: Maybe Char -> State AutomataInfo ()
    setRecentEdge edge = do { info <- get; put $ info { recentEdge = edge }; return () }
    updateFunc func node edge target =
      if edge == '.' then (\n e -> if n == node then return target else func n e)
      else (\n e -> if n == node && e == edge then return target else func n e)
    addSelfRing :: Integer -> Char -> State AutomataInfo ()
    addSelfRing node edge = modify $ \info -> info { transition = updateFunc (transition info) node edge node }
    addCurNodeToThroughNodes = do
      info <- get
      node <- getCurNode
      put $ info { throughNodes = node : throughNodes info }
    createNewNode = do
      info <- get
      let count = nodeCount info
      put $ info { nodeCount = count + 1 }
      return count
    addNewEdge :: Integer -> Char -> Integer -> State AutomataInfo ()
    addNewEdge source edge target =
      modify $ \info -> info { transition = updateFunc (transition info) source edge target }
    setCurNode :: Integer -> State AutomataInfo ()
    setCurNode node = modify $ \info -> info { curNode = node }
    clearThroughNodes = modify $ \info -> info { throughNodes = [] }
    setFinalNodes :: [Integer] -> State AutomataInfo ()
    setFinalNodes nodes = modify $ \info -> info { acceptingNodes = nodes }

automataParse :: String -> AutomataInfo
automataParse str =
  execState (automataParserState str) $ AutomataInfo {
    nodeCount = 1,
    curNode = 0,
    transition = \_ _ -> Nothing,
    acceptingNodes = [],
    throughNodes = [0],
    recentEdge = Nothing
  }

matchString :: (Num s) => (s -> Char -> Maybe s) -> String -> Maybe s
matchString trans = List.foldl (\s c -> s >>= (`trans` c)) (return 0)

-- Viable but more complex versions
-- matchString :: (Foldable t1, Num (m t2), Monad m) => (t2 -> a -> t2) -> t1 a -> m t2
-- matchString trans str =
--   (0 &) $
--   execState $
--   forM_ str $ \c -> do
--     state <- get 
--     let nextState = do { ts <- state; return $ trans ts c }
--     put nextState

-- matchString :: Num a1 => (a1 -> a2 -> Maybe a1) -> [a2] -> State (Maybe a1, [a2]) ()
-- matchString trans str = do
--   cfor (Just 0, str) (\(_, rst) -> case rst of { _:_ -> True; [] -> False }) nextStr $ do
--     (state, ~str@(h:_)) <- get
--     let nextState = do { ts <- state; return $ trans ts h }
--     put (nextState, str)
--   where
--     nextStr :: State (Maybe a, [b]) ()
--     nextStr = do
--       (x, ~(_:y)) <- get 
--       put (x, y)
  -- while (\(_, rst) -> case rst of { _:_ -> True; [] -> False }) $ do
  --   (state, (h:))


matchOneStringWithPattern :: String -> String -> Bool
matchOneStringWithPattern str patStr =
  let pattern = printPatternString $ patternNomalisation $ parsePattern patStr in
  trace ("Normalised Pattern String: \"" ++ pattern ++ "\"") $
  let automata = automataParse $ trimWhiteSpace pattern in
  let res = (str &) $ matchString $ transition automata in
  fromMaybe False $ res <&> (`elem` acceptingNodes automata)
  where
    trimWhiteSpace (h:str)
      | h `elem` " \t\n\r" = trimWhiteSpace str
      | otherwise = h : trimWhiteSpace str
    trimWhiteSpace [] = []

{-| Find length of a given number

>>> findNumberLength 12000000
8
-}
findNumberLength :: (Integral a, Integral b) => a -> b
findNumberLength n = snd $ execState prog (n, 0)
  where
    prog = do
      while ((/= 0) . fst) $ do
        n <- getN
        putN $ n `div` 10
        addRes
      where
        getN = fst <$> get
        putN :: n -> State (n, m) ()
        putN n = modify (\(a, b) -> (n, b))
        -- addRes :: (Num m) => State (n, m) ()
        addRes = modify (\(a, b) -> (a, b + 1))

data MatchPattern = Single Char | Any | Star Char | StarAny deriving (Eq, Ord)

instance Show MatchPattern where
  show pat =
    case pat of
      Single c -> [c]
      Any      -> "."
      Star c   -> c:"*"
      StarAny  -> ".*"

printPatternString :: [MatchPattern] -> [Char]
printPatternString patStr = do
  pat <- patStr
  show pat

parsePattern :: String -> [MatchPattern]
parsePattern str =
  case str of
    c:'*':str ->
      if c == '*' then error "Invalid Pattern"
      else if c == '.' then StarAny : parsePattern str
      else Star c : parsePattern str
    c:str ->
      if c == '*' then error "Invalid Pattern"
      else if c == '.' then Any : parsePattern str
      else Single c : parsePattern str
    [] -> []

{-| Normalise the pattern string and obtain a normalised match pattern

"a*.*" === ".*"
"a*a"  === "aa*"
"a*a*" === "a*"
".*a*" === ".*"
-}
patternNomalisation :: [MatchPattern] -> [MatchPattern]
patternNomalisation pat = 
  case pat of
    -- .*. === ..*
    StarAny:Any:pat -> Any:patternNomalisation (StarAny:pat)
    -- .*.* === .*
    StarAny:StarAny:pat -> patternNomalisation $ StarAny:pat
    -- .*a* === .*
    StarAny:Star c:pat -> patternNomalisation $ StarAny:pat
    -- a*.* === .*
    Star c:StarAny:pat -> patternNomalisation $ StarAny:pat
    -- a*a* === a*
    Star a:Star b:pat -> 
      if a == b then patternNomalisation $ Star a : pat
      else Star a : patternNomalisation (Star b : pat)
    -- a*a  === aa*
    Star a:Single b:pat -> 
      if a == b then Single a : patternNomalisation (Star a:pat)
      else Star a:Single b:patternNomalisation pat
    p:pat -> p : patternNomalisation pat
    [] -> []

-- solve non-determinism through building units
buildUnits pattern =
  let pat = patternNomalisation pattern in
  undefined
