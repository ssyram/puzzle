module Calculator where

import Debug.Trace

-- A Quick Implementation of Simple Calculator

computeVal :: String -> Maybe Rational
computeVal s =
  let tokenStream = getTokenStream s in
  -- trace (show $ take 10 tokenStream) $
  compute tokenStream [] []
  where
    getTokenStream s = let (h, ns) = head $ lex s in h:getTokenStream ns
    -- allOps = ['+', '-', '*', '/']
    singleStepCompute :: Char -> [Rational] -> Maybe [Rational]
    singleStepCompute op numStack =
      if length numStack < 2 then Nothing
      else
        let n1:n2:numStack' = numStack in
        let n = case op of '+' -> n1 + n2
                           '-' -> n2 - n1
                           '*' -> n1 * n2
                           '/' -> n2 / n1
                           _   -> error "Impossible"
        in Just $ n:numStack'
    popUntil :: [Rational] -> [Char] -> [Char] -> Maybe ([Rational], [Char])
    popUntil numStack (op:opStack) popLst =
      if op `notElem` popLst then do
        numStack <- singleStepCompute op numStack
        popUntil numStack opStack popLst
      else Just (numStack, op:opStack)
    popUntil ns [] _ = Just (ns, [])
    compute :: [String] -> [Rational] -> [Char] -> Maybe Rational
    compute [] numStack _ =
      if tail numStack /= [] then Nothing
      else Just $ head numStack
    compute (s:ss) numStack opStack =
      case s of
        ['+'] -> plusMinus '+'
        ['-'] -> plusMinus '-'
        ['('] -> compute ss numStack ('(':opStack)
        [')'] -> do
          (ns, ops) <- popUntil numStack opStack "("
          if null ops || head ops /= '(' then Nothing
          else compute ss ns $ tail ops
        ['*'] -> mulDiv '*'
        ['/'] -> mulDiv '/'
        ""    -> do
          (ns, ops) <- popUntil numStack opStack "("
          if not (null ops) || length ns /= 1 then Nothing
          else return $ head ns
        num   ->
          let res = readsPrec 1 num :: [(Double, String)] in
          -- trace (show res) $
          if null res || not (null (tail res)) then Nothing
          else
            let (n, s) = head res in
            if null s then compute ss (toRational n:numStack) opStack
            else Nothing
        where
          plusMinus s = do
            (ns, ops) <- popUntil numStack opStack "("
            compute ss ns (s:ops)
          mulDiv s = do
            (ns, ops) <- popUntil numStack opStack "(+-"
            compute ss ns (s:ops)

-- x :: [Integer]
-- x = [
--   1966,
--   1972,
--   1974,
--   1976,
--   1977,
--   1978,
--   1979,
--   1980,
--   1984,
--   1987,
--   1991,
--   1996,
--   2001,
--   2003,
--   2005,
--   2006,
--   2007,
--   2008,
--   2011,
--   2020
--   ]