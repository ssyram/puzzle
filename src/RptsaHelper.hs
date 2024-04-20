{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
-- | This file is for helping rPTSA-PAHORS tool
module RptsaHelper () where

import Utils
import Data.Ord (Down)
import Prelude hiding ((/), (-))

genRptsaHeader :: (Show a1, Show a2, Show a3, Show a4) =>
  String -> a1 -> a2 -> a3 -> a4 -> String
genRptsaHeader letDefs k q0 m0 g0 =
  [
    "%BEGIN rPTSA config",
    "restriction := " ++ show k,
    "q0 := " ++ show q0,
    "m0 := " ++ show m0,
    "gamma0 := " ++ show g0,
    "%END rPTSA config"
  ]
  |> concat
  |> (letDefs ++)

-- printing Tricks -- in order to write (definedInF#)
data DefinedInF = DefinedInF
data Project = Project
-- the only operator to definedInF
(#) :: DefinedInF -> Project -> a
(#) _ = error "Already defined in the F# project"
-- the only parameter to be postfixed by #
definedInF :: DefinedInF
definedInF = DefinedInF

{- | Generate the sequential_loops example, which cannot be handled by Amber 

- initialise the value of `x`:
(qX0, m0, root) -> (qX0, m0, up loop)
- 0 <= i <= 9:
(qX{i}, m0, loop) -> (qX{i + 1}, mLower, up loop)
- 10 <= i <= 97:
(qX{i}, m0, loop) -> (qX{i + 1}, mUsual, up loop)
- 98 <= i <= 99:
(qX{i}, m0, loop) -> (qX{i + 1}, mReached, up loop)
(qX100, m0, loop) -> (qBack, mReached, down)

- get back to start `y`:
(qBack, {All M}, loop) -> (qBack, {Original M}, down)
- start `y`:
(qBack, m0, root) -> (YL1_0, m0, up loop)
- run first loop (L1) for `y`:
(YL1_0, {All M but mReached}, loop) 
  ->(1/3) (YL1_0, {Original M}, up loop)
  ->(1/3) (YL1_1, {Original M}, up loop)
  ->(1/3) (YL1_2, {Original M}, up loop)
- relay rules for `y`: 0 < i <= 2
(YL1_{i}, {All M}, loop) -> (YL1_{i - 1}, {All M}, up loop)
- reached, end the first loop for `y`:
(YL1_0, mReached, loop) -> YL2_0
- start getting into the second loop for `y`:
(YL2_0, {All M but m Lower}, loop)
  ->(1/3) YL2_0
  ->(2/3) (YL2_9, m0, down)
- relay rules: 0 < i <= 9
(YL2_{i}, {All M}, loop) -> (YL2_{i - 1}, m0, down)
- reached lower, end the second loop for `y`:
(YL2_0, mReached, loop) -> (qEnd, m0, down)
- terminate at the bottom
(qEnd, m0, root) -> \top
-}
sequentialLoopsRules :: a
sequentialLoopsRules = definedInF#Project


newtype State = Q String
newtype LocMem = M String
newtype Gamma = G String

(/) a b = show a ++ "/" ++ show b

(-) p op = (p, op)

newtype Probability = P String deriving (Eq, Ord)
data Operator =
    OpState !State
  | OpLocMem !LocMem
  | OpUp !State !LocMem !Gamma
  | OpDown !State !LocMem
  | OpTer

pOne :: Probability
pOne = P "1"

class RightHandSide t where
  toPWithOp :: t -> (Probability, Operator)

data PrimitiveOperator =
    Up !Gamma
  | Down

data Termination = Ter

instance RightHandSide (State, LocMem, PrimitiveOperator) where
  toPWithOp (q, m, pop) = 
    case pop of
      Up g -> (P "1", OpUp q m g)
      Down -> (P "1", OpDown q m)

class AbsProbability p where
  toProbability :: p -> Probability

instance (RightHandSide op, AbsProbability p) => RightHandSide (p, op) where
  toPWithOp (p, consOp) = 
    let (p', op) = toPWithOp consOp in
    if p' /= P "1" then error "" else
    (toProbability p, op)

instance AbsProbability String where
  toProbability = P

instance RightHandSide Termination where
  toPWithOp Ter = (pOne, OpTer)

instance AbsProbability Double where
  toProbability :: Double -> Probability
  toProbability p = P $ show p

infix 3 -->

infix 5 /

infix 4 -

(-->) :: RightHandSide t => (State, LocMem, Gamma) -> t -> (State, LocMem, Gamma, Probability, Operator)
(q, m, g) --> rhs =
  let (p, op) = toPWithOp rhs in
  (q, m, g, p, op)

instance RightHandSide State where
  toPWithOp st = (pOne, OpState st)

rules =
  let q = Q "q"
      m = M "m"
      root = G "root"
  in
  [
    (q, m, root) --> 1 / 2 - q,
    (q, m, root) --> 1 / 2 - Ter
  ]
