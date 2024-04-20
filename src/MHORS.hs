{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
module MHORS where

import qualified Data.List as List
import Data.Maybe
import Utils
import Test.QuickCheck
import Data.Ratio

-- The file for recording MHORS-related stuff
-- currently consider ONLY string generting (non-deterministic) MHORS

data Type =
    Base
  | LApp Type Type
  deriving (Eq, Ord)

data SymbolType s =
    Terminal s
  | NonTerminal s 
  | Variable s 
  | TerminateMark

-- | the class that the type of the symbol in terms should satisfy
class TermSymbol s where
  isVar :: s -> Bool 

instance TermSymbol (SymbolType s) where
  isVar = \case Variable _ -> True; _ -> False 

data Term s where
  Symbol :: (TermSymbol s) => s -> Term s
  App    :: Term s -> Term s -> Term s 

tryTyping :: Eq a => (a -> Type) -> Term a -> Maybe (Type, [a])
tryTyping typingEnv t =
  case t of
    Symbol s -> return (typingEnv s, [s | isVar s])
    App t1 t2 -> do
      (ty1, vars1) <- tryTyping typingEnv t1
      (ty2, vars2) <- tryTyping typingEnv t2
      if not $ null $ vars1 `List.intersect` vars2
        then Nothing
        else case ty1 of
          LApp arg ret -> if arg /= ty2 then Nothing else return (ret, vars1 ++ vars2)
          Base         -> Nothing

(|-) :: Eq a => (a -> Type) -> Term a -> Maybe Type
typingEnv |- t = fst <$> tryTyping typingEnv t

data AppNormalForm s = AppNormalForm s [AppNormalForm s]

toAppNormalForm :: Term s -> AppNormalForm s
toAppNormalForm (Symbol s) = AppNormalForm s []
toAppNormalForm (App f a) = 
  let (AppNormalForm s lst) = toAppNormalForm f in 
  AppNormalForm s $ lst ++ [toAppNormalForm a]

data BRoseTree a = BRoseTree a [BRoseTree a] [BRoseTree a]

p :: Double
p = 0.5

flipp :: Double -> Gen Bool 
flipp p = do
  n :: Double <- arbitrary
  return $ n - fromIntegral (floor n) > p

genList :: (Arbitrary a) => Gen [a]
genList = do
  endGen <- flipp p
  if endGen 
    then return []
    else do
      this <- arbitrary 
      rest <- genList
      return $ this : rest
  
genSameLengthList :: Arbitrary a1 => [a2] -> Gen [a1]
genSameLengthList [] = return []
genSameLengthList (_:xs) = do
  this <- arbitrary 
  rest <- genSameLengthList xs
  return $ this : rest

instance Arbitrary a => Arbitrary (BRoseTree a) where
  arbitrary = do
    a <- arbitrary 
    lhs <- genList 
    rhs <- genSameLengthList lhs
    return $ BRoseTree a lhs rhs
