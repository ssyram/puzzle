{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
module NewFormula where

import Control.Monad
import Control.Monad.ST
import Data.STRef


class Formula f
class InfixOperator op
class Environment env
class Variable v
-- formula attached wit information
instance Formula f => Formula (f, info)

-- Various kinds of formulas
-- | formula with infix operators, which is a special kind of environment
data FormulaInfix op f1 f2 where
  FormulaInfix :: (InfixOperator op, Formula f1, Formula f2) =>
    op -> f1 -> f2 -> FormulaInfix op f1 f2
instance Formula (FormulaInfix op f1 f2)
-- | Formula Environement, introduce multiple environment
data FormulaEnv env f where
  FormulaEnv :: (Environment env, Formula f) => env -> [f] -> FormulaEnv env f
instance Formula (FormulaEnv env f)
-- | a new environment that introduces new bounded variable
data FormulaLambda v f where
  FormulaLambda :: (Variable v, Formula f) => v -> f -> FormulaLambda v f
instance Formula (FormulaLambda v f)
data FormulaAtom p v where
  FConst :: p -> FormulaAtom p v
  FVar :: (Variable v) => v -> FormulaAtom p v
instance Formula (FormulaAtom p v)

-- Variable(s)
-- | variable constructors
data VarCoumpound pv f where
  CompoundVar :: (Eq pv, Formula f) => pv -> [f] -> VarCoumpound pv f
instance Variable (VarCoumpound pv f)
-- | atomic variable, as a special kind of compound variable
data VarAtom pv where
  AtomVar :: (Eq pv) => pv -> VarAtom pv
instance Variable (VarAtom pv)

class HasInfo t info where getInfo :: t -> info
instance HasInfo (x, info) info where getInfo = snd 

class (Formula f, Formula tf, HasInfo tf info) => AttachInfoM f tf info where
  attachInfoM :: (Monad m) => (forall f. (Formula f) => f -> m info) -> f -> m tf

instance (AttachInfoM f1 fi1 info, AttachInfoM f2 fi2 info) =>
  AttachInfoM (FormulaInfix op f1 f2) (FormulaInfix op fi1 fi2, info) info where
    attachInfoM genInfo f@(FormulaInfix op f1 f2) = do
      info <- genInfo f
      f1 <- attachInfoM genInfo f1
      f2 <- attachInfoM genInfo f2
      return (FormulaInfix op f1 f2, info)
instance AttachInfoM (FormulaAtom p v) (FormulaAtom p v, info) info where
    attachInfoM genInfo f = do
      info <- genInfo f
      return (f, info)
instance (AttachInfoM f fi info) =>
  AttachInfoM (FormulaEnv env f) (FormulaEnv env fi, info) info where
    attachInfoM genInfo f@(FormulaEnv env lst) = do
      info <- genInfo f
      lst <- forM lst $ attachInfoM genInfo
      return (FormulaEnv env lst, info)
instance (AttachInfoM f fi info) => 
  AttachInfoM (FormulaLambda v f) (FormulaLambda v fi, info) info where
    attachInfoM genInfo f@(FormulaLambda v nf) = do
      info <- genInfo f 
      nf <- attachInfoM genInfo nf
      return (FormulaLambda v nf, info)

index :: (AttachInfoM f tf Integer) => f -> tf
index f =
  runST $ do
  nextIdx <- newSTRef 0
  attachInfoM (\_ -> do idx <- readSTRef nextIdx; writeSTRef nextIdx (idx + 1); return idx) f


