{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
module ExprProbFormula where

import Data.Data
import GHC.Generics
import Data.Hashable

-- the implementation of normal method to solve the expression problem to formulas
-- formal comparison must be implemented

data Commutativity =
    FullCommutative
  -- | means its reverse operator 
  | RevCommutative
  | NonCommutative

-- | formula is just a kind of type class, "what can be called a formula"
class (Eq f) => Formula f
-- | "what can be called a variable", variables must be comparable
class (Eq v) => Variable v
class (Eq op) => InfixOperator op where
  getAssoc :: op -> Associativity  
  getCommut :: op -> Commutativity

data BasicVariable pv f =
  --   BVPrimitive pv
  -- | BVUnary pv f 
  -- | VBBinary pv f f
  -- | VBTernary pv f f f 
  -- | VBArity4 pv f f f f 
  BasicVariable pv Int [f]  -- primitive variable, arity and actual constructive arguments
  deriving (Eq, Show, Ord)
instance (Formula f, Eq pv) => Variable (BasicVariable pv f)
-- a basic variable is also a formula
instance (Formula f, Eq pv) => Formula (BasicVariable pv f)
instance (Formula f, Eq info) => Formula (f, info)

-- toGeneral :: BasicVariable pv f -> BasicVariable pv f
-- toGeneral = \case
--   BVPrimitive pv -> VBGeneral pv []
--   BVUnary pv f -> VBGeneral pv [f]
--   VBBinary pv f f' -> VBGeneral pv [f, f']
--   VBTernary pv f f' f'' -> VBGeneral pv [f, f', f'']
--   VBArity4 pv f1 f2 f3 f4 -> VBGeneral pv [f1, f2, f3, f4]
--   v -> v 

-- | infix formula
data InfixFormula op f1 f2 = InfixFormula op f1 f2 deriving (Eq, Show, Ord)
instance (InfixOperator op, Formula f1, Formula f2) => Formula (InfixFormula op f1 f2)
-- | function apply formula
data FFunctionApply v f = FFunctionApply v f deriving (Eq, Show, Ord)
instance (Variable v, Formula f) => Formula (FFunctionApply v f)
-- | env formula
data FEnv env v r f = FEnv env v r f deriving (Eq, Show, Ord)
instance (Variable v, Formula r, Formula f, Eq v, Eq r, Eq env) => Formula (FEnv env v r f)

data BasicInfixOp =
    OpAdd
  | OpMul
  | OpDiv
  | OpMinus
  deriving (Eq, Show, Ord, Generic, Hashable)
instance InfixOperator BasicInfixOp where
  getAssoc _ = LeftAssociative 
  getCommut = \case
    OpAdd -> FullCommutative
    OpMul -> FullCommutative
    OpDiv -> RevCommutative
    OpMinus -> RevCommutative

-- | we have that: `ti` is the number
class (Formula t, Formula ti) => FormulaIndex t ti where -- indexed with formula 
  index :: Integer -> t -> (ti, Integer)  -- this index and the next index

instance (FormulaIndex f1 f1i, FormulaIndex f2 f2i, InfixOperator op) => 
  FormulaIndex (InfixFormula op f1 f2) (InfixFormula op f1i f2i, Integer) where
    index nextIdx (InfixFormula op f1 f2) = 
      let (f1i, next) = index (nextIdx + 1) f1 in
      let (f2i, ret) = index next f2 in 
      ((InfixFormula op f1i f2i, nextIdx), ret)

instance (Variable v, FormulaIndex r ri, FormulaIndex f fi, Eq env) => 
  FormulaIndex (FEnv env v r f) (FEnv env v ri fi, Integer) where
    index nextIdx (FEnv env v r f) = 
      let (ri, next) = index (nextIdx + 1) r in
      let (fi, ret) = index next f in
      ((FEnv env v ri fi, nextIdx), ret)


