{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
module HORSTypingTest where

import Utils
import Control.Monad.Writer hiding (Product)
import Control.Monad.Trans.Maybe
import Control.Applicative
import Data.List (sort, groupBy)

data Type =
    Base
  | TypeVar Int  -- `Int` to indicate the index of the type variable to distinguish from other types
  | Product Type Type
  | Function Type Type

data Term s =
    Symbol s
  | Pairing (Term s) (Term s)
  | Application (Term s) (Term s)
  | Projection Int (Term s)


solveTypeEquationalInformation eqLst = do
  -- [(typeVarName, Type)]
  uniqueTypeInfo <- solveUniqueType $ groupVarInfo eqLst
  undefined 
  where
    solveUniqueType = undefined 
    groupVarInfo = undefined 
  -- groupVarInfo eqLst  -- [(typeVarName, [Type])]
  -- > solveUniqueType  -- Maybe [(typeVarName, Type)]
  -- > 

-- | see if two given type can be unified to one single type
solveType :: Type -> Type -> Maybe Type
solveType t t' = do
  eqInfo <- extractEqInfo $ collectEqInfo t t'
  (leftSubsInfo :: [(Int, Type)]) <- solveEqInfo eqInfo
  return $ substituteType leftSubsInfo t
  where
    solveEqInfo = undefined

    substituteType :: (Foldable t) => t (Int, Type) -> Type -> Type
    substituteType subsInfo = \case
      Base -> Base
      TypeVar idx -> foldl (\ft (i, t) -> if i == idx then t else ft) (TypeVar idx) subsInfo
      Product t1 t2 -> Product (substituteType subsInfo t1) (substituteType subsInfo t2)
      Function t1 t2 -> Function (substituteType subsInfo t1) (substituteType subsInfo t2)

    extractEqInfo :: MaybeT (Writer info) b -> Maybe info
    extractEqInfo info =
      let (x, ret) = runWriter $ runMaybeT info in
      fmap (const ret) x

    collectEqInfo :: MonadWriter [(Either Int Int, Type)] m => Type -> Type -> MaybeT m Type
    collectEqInfo t t' =
      case (t, t') of
        (Base, Base) -> return Base
        (TypeVar lIdx, _) -> do
          lift $ tell [(Left lIdx, t')]
          return t'
        (_, TypeVar rIdx) -> do
          lift $ tell [(Right rIdx, t)]
          return t
        (Product t1 t2, Product t1' t2') -> do
          t1 <- collectEqInfo t1 t1'
          t2 <- collectEqInfo t2 t2'
          return $ Product t1 t2
        (Function t1 t2, Function t1' t2') -> do
          t1 <- collectEqInfo t1 t1'
          t2 <- collectEqInfo t2 t2'
          return $ Function t1 t2
        (_, _) -> MaybeT $ return Nothing 

someTest :: MaybeT (Writer String) ()
someTest = do
  lift $ tell "a"

collectEqInfo :: MonadWriter [(Either Int Int, Type)] m => Type -> Type -> MaybeT m Type
collectEqInfo t t' =
  case (t, t') of
    (Base, Base) -> return Base
    (TypeVar lIdx, _) -> do
      lift $ tell [(Left lIdx, t')]
      return t'
    (_, TypeVar rIdx) -> do
      lift $ tell [(Right rIdx, t)]
      return t
    (Product t1 t2, Product t1' t2') -> do
      t1 <- collectEqInfo t1 t1'
      t2 <- collectEqInfo t2 t2'
      return $ Product t1 t2
    (Function t1 t2, Function t1' t2') -> do
      t1 <- collectEqInfo t1 t1'
      t2 <- collectEqInfo t2 t2'
      return $ Function t1 t2
    (_, _) -> MaybeT $ return Nothing 

-- anotherCollectEqInfo :: Type -> Type -> WriterT [(Either Int Int, Type)] Maybe Type
anotherCollectEqInfo :: (MonadWriter [(Either Int Int, Type)] m, Alternative m) =>
  Type -> Type -> m Type
anotherCollectEqInfo t t' =
  case (t, t') of
    (Base, Base) -> return Base
    (TypeVar lIdx, _) -> do
      tell [(Left lIdx, t')]
      return t'
    (_, TypeVar rIdx) -> do
      tell [(Right rIdx, t)]
      return t
    (Product t1 t2, Product t1' t2') -> do
      t1 <- anotherCollectEqInfo t1 t1'
      t2 <- anotherCollectEqInfo t2 t2'
      return t'
    (Function t1 t2, Function t1' t2') -> do
      t1 <- anotherCollectEqInfo t1 t1'
      t2 <- anotherCollectEqInfo t2 t2'
      return $ Function t1 t2
    (_, _) -> empty
