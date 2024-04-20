{-# LANGUAGE Strict #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
module ProgHelper where

import Data.Hashable (Hashable)
import Utils (sndMap)

#define STD_DERIVING deriving (Show, Eq, Ord, Read)

-- This file is for the implementation of a prototype algorithm for minimising the location
-- of the target CFA


-- There is no need for the following definition -- what we need is just to implement a to-CFA algorithm

-- data ArithOp
--   = Add
--   | Minus
--   | Mul
--   | Div

-- data BoolOp
--   = And
--   | Or

-- -- | A template type of `Expr`
-- data Expr v t where
--   EVar :: v -> Expr v t  -- Var may of any type
--   EArith :: (Num n) => ArithOp -> Expr v n -> Expr v n -> Expr v n
--   ECmp :: (Num n) => Ordering -> Expr v n -> Expr v n -> Expr v Bool
--   EBoolNot :: Expr v Bool -> Expr v Bool
--   EBool :: BoolOp -> Expr v Bool -> Expr v Bool -> Expr v Bool

-- -- | A Type of Program with `p` for probability type,
-- --   `v` for variable type,
-- --   `e` for expression constructor type that accepts the variable type
-- --   also accepts the type to determine the actual type of the program
-- data Program p v e where
--   Assn :: (Num n) => v -> e v n -> Program p v e
--   If :: e v Bool -> Program p v e -> Program p v e -> Program p v e
--   While :: e v Bool -> Program p v e -> Program p v e
--   NonDet :: [Program p v e] -> Program p v e
--   Seq :: Program p v e -> Program p v e -> Program p v e
--   Prob :: (Fractional p) => [(p, Program p v e)] -> Program p v e
--   Skip :: Program p v e

data Var where
  Var :: String -> Var
  STD_DERIVING

data IntExpr where
  IEConst :: Int -> IntExpr
  STD_DERIVING

data BoolExpr
  STD_DERIVING

newtype Probability = Probability Rational
  STD_DERIVING

data Program where
  Assn :: Var -> IntExpr -> Program
  If :: BoolExpr -> Program -> Program -> Program
  While :: BoolExpr -> Program -> Program
  NonDet :: [Program] -> Program
  Seq :: Program -> Program -> Program
  Prob :: [(Probability, Program)] -> Program
  Skip :: Program

newtype DistTag where
  DistTag :: Int -> DistTag
  STD_DERIVING

newtype BranchTag = BranchTag Int
  STD_DERIVING

newtype NonDetTag = NonDetTag Int
  STD_DERIVING

data EdgeStmt
  = ESAssn Var IntExpr
  | ESAssume BoolExpr
  | ESProb DistTag BranchTag Rational  -- the distribution tag, branch tag and the actual value
  | ESNonDet
  STD_DERIVING

-- Add the functionalities of keeping loop information to `Node`

data SingleAssn = SingleAssn Var IntExpr
  STD_DERIVING

data Node where
  NNormal :: SingleAssn -> Node -> Node
  NBIf :: [(BoolExpr, Node)] -> Node
  NBProb :: DistTag -> [(Probability, Node)] -> Node
  NBNonDet :: [Node] -> Node
  NLoop :: {loopSt :: Node, next :: Node} -> Node
  NLeaf :: Node  -- the final point of the node
  STD_DERIVING

-- >>> appNode (NNormal (SingleAssn (Var "a") $ IEConst 1) NLeaf) NLeaf
-- NNormal (SingleAssn (Var "a") (IEConst 1)) NLeaf
appNode :: Node -> Node -> Node
appNode above below =
  case above of
    NNormal assn next -> NNormal assn $ appNode next below
    NLeaf -> below
    NLoop loopSt next -> NLoop loopSt $ appNode next below
    NBIf lst -> NBIf $ flip fmap lst $ sndMap $ flip appNode below
    NBProb distTag lst -> NBProb distTag $ flip fmap lst $ sndMap $ flip appNode below
    NBNonDet lst -> NBNonDet $ flip fmap lst $ flip appNode below



-- Try to implement the statement concat function here

data SingleStatement
  = SSAssn SingleAssn
  | SSAssume BoolExpr
  | SSNonDet NonDetTag
  | SSProb DistTag BranchTag
  STD_DERIVING
newtype SeqStatements = SeqStatements [SingleStatement]
  STD_DERIVING
data Statement
  = SSingle SingleStatement
  | SSeq SeqStatements
  STD_DERIVING

data StatementType
  = STProb
  | STAssumption
  | STNormal
  STD_DERIVING

getType :: Statement -> StatementType
getType (SSeq (SeqStatements [])) = STNormal
getType (SSeq (SeqStatements (x:_))) = getType $ SSingle x
getType (SSingle (SSAssn _)) = STNormal
getType (SSingle (SSAssume _)) = STAssumption
getType (SSingle (SSNonDet _)) = STNormal
getType (SSingle (SSProb _ _)) = STProb

matchType :: StatementType -> StatementType -> Maybe StatementType
matchType STNormal t2 = Just t2
matchType t1 STNormal = Just t1
matchType STProb STProb = Just STProb
matchType STAssumption STAssumption = Just STAssumption
matchType _ _ = Nothing

tryConcatStmts st1 st2 =
  let ty1 = getType st1
      ty2 = getType st2
  in do
  ty <- matchType ty1 ty2
  case ty of
    STNormal -> undefined
    STProb -> undefined
    STAssumption -> undefined

data State

newtype ProbDist where
  ProbDist :: [(Probability, [SingleStatement], State)] -> ProbDist

newtype ProbBranchSets where
  ProbBranchSets :: [ProbDist] -> ProbBranchSets

newtype AssumptionBranchesSets =
  AssumptionBranchesSets [(BoolExpr, [SingleStatement], State)]

{- | Cartesian product of lists

>>> distributeComp []
[[]]

>>> distributeComp [[1, 2], [3, 4, 5]]
[[1,3],[1,4],[1,5],[2,3],[2,4],[2,5]]

>>> distributeComp [[1, 2], [3, 4], [5, 6, 7]]
[[1,3,5],[1,3,6],[1,3,7],[1,4,5],[1,4,6],[1,4,7],[2,3,5],[2,3,6],[2,3,7],[2,4,5],[2,4,6],[2,4,7]]

>>> distributeComp [[1, 2], [], [3]]
[]
-}
distributeComp :: [[a]] -> [[a]]
distributeComp [] = [[]]
distributeComp (lst : rest) = do
  e <- lst
  l <- distributeComp rest
  return $ e : l

data Val d
  = Val d
  | ANY

isAny :: Val a -> Bool
isAny ANY = True
isAny _   = False



