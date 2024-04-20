{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
module Formula where

import Utils
import Control.Monad
import Control.Monad.ST.Strict
import Data.STRef.Strict
import Control.Monad.Identity
import Test.QuickCheck
import GHC.Generics
import Data.Hashable
import Debug.Trace
import Data.Ratio

{-| ==== Basic Formula Type

  The basic formula type we tackle

  SPECIAL NOTE: 
    This structure should be *determined*, any further extension should be in `sp`.

  We'll assume the whole basic formula satisfies some specific rules, which are specified in
  operation functions.
  Those will violate the rule should be in `sp`.
  For example, we assume the independentness across different types of constructors.
  Syntactic sugers like (1 : [2, 3]) cannot be recognised and translation cannot be performed.

  /Type Parameters/
  * `sp`: special operation, for future extension
  * `pop`: prefix operator type
  * `iop`: infix operator type
  * `env`: environment type, means to introduce a new variable to the new environment
  * `p`: the number type
  * `v`: the type of variables
  * `a`: the type of information attached
-}
data Formula sp pop iop env p v a =
  -- | constant value
    FConst p
  -- | variable
  | FVar v
  -- | prefix opearator
  | FPrefix pop (InfoFormula sp pop iop env p v a)
  -- | infix opearator
  | FInfix iop (InfoFormula sp pop iop env p v a) (InfoFormula sp pop iop env p v a)
  -- | environment, introduce a new variable with a "bound" formula and a content operator
  | FEnv env v (InfoFormula sp pop iop env p v a) (InfoFormula sp pop iop env p v a)
  -- | multiple formulas
  | FList [InfoFormula sp pop iop env p v a]
  -- | special operator, develop for future use
  | FSpecial sp
  deriving (Show, Generic, Hashable)

{-| The type of formula attached with information of type `a`. -}
newtype InfoFormula sp pop iop env p v a = InfoFormula (Formula sp pop iop env p v a, a)
  deriving (Show, Generic, Hashable)

-- no generic arbitrary implementation
instance
  (Arbitrary pop, Arbitrary iop, Arbitrary env, Arbitrary p, Arbitrary v, Arbitrary a) =>
  Arbitrary (InfoFormula () pop iop env p v a) where
  arbitrary = InfoFormula <$> ((,) <$> arbitrary <*> arbitrary)

{-
  An AST problem -- how to design a system that is AST.
  Also compute the expected termination time to guard the whole thing.
  will NOT generate special operations

  The key is to distribute probabilities, actually, we can distribute things accroding to its re-producibility
-}
instance
  (Arbitrary pop, Arbitrary iop, Arbitrary env, Arbitrary p, Arbitrary v, Arbitrary a) =>
  Arbitrary (Formula () pop iop env p v a) where
  arbitrary = do
    kInit <- arbitrary :: Gen Int 
    let k = abs kInit + 1  -- to prevent k from being 0
    x <- sampleUniform  -- sample uniformly from [0, 1]
    -- () <- trace ("k = " ++ show k ++ "Value = " ++ show (fromRational x :: Double)) return ()
    case numConstruct x (fromIntegral k) of
      0 -> do
        cons <- sampleConstructor 2
        case cons of
          0 -> FConst <$> arbitrary
          1 -> FVar <$> arbitrary
          _ -> eIMPOSSIBLE 
      1 -> FPrefix <$> arbitrary <*> arbitrary
      2 -> do
        cons <- sampleConstructor 2
        case cons of
          0 -> FInfix <$> arbitrary <*> arbitrary <*> arbitrary
          1 -> FEnv <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
          _ -> eIMPOSSIBLE 
      _ -> FList <$> fmap (take k) arbitrary 
    where
      sampleUniform = do
        frac <- arbitrary :: Gen Rational 
        let top = abs $ numerator frac 
        let below = abs $ denominator frac 
        if top <= below then return frac else return $ top `mod` below % below
      numConstruct value k
        | value < p1 = 0
        | value < p2 = 1
        | value < p3 = 2
        | otherwise  = 3
        where p1 = 1 % 2
              p2 = p1 + k % (3 * k + 2)
              p3 = p2 + k % (6 * k + 4)
      sampleConstructor n = do
        cons <- arbitrary :: Gen Int 
        return $ abs cons `mod` n


data FormulaMapper sp pop iop env p v a sp' pop' iop' env' p' v' a' =
  FormulaMapper {
    mapSp :: sp -> sp',
    mapPrefix :: pop -> pop',
    mapInfix :: iop -> iop',
    mapEnv :: env -> env',
    mapConst :: p -> p',
    mapVar :: v -> v',
    mapInfo :: a -> a'
  }
retMapper :: (Monad m) => FormulaMapper sp pop iop env p v a (m sp) (m pop) (m iop) (m env) (m p) (m v) (m a)
retMapper = FormulaMapper {
  mapSp=return, mapPrefix=return,
  mapInfix=return, mapEnv=return,
  mapConst=return, mapVar=return,
  mapInfo=return}
transformM :: (Monad m) =>
  FormulaMapper sp pop iop env p v a (m sp') (m pop') (m iop') (m env') (m p') (m v') (m a') ->
  InfoFormula sp pop iop env p v a -> m (InfoFormula sp' pop' iop' env' p' v' a')
transformM f (InfoFormula (ef, info)) = do
  info <- mapInfo f info
  efm <- case ef of FConst c -> FConst <$> mapConst f c
                    FVar v -> FVar <$> mapVar f v
                    FPrefix op efi -> FPrefix <$> mapPrefix f op <*> transformM f efi
                    FInfix op f1 f2 -> FInfix <$> mapInfix f op <*> transformM f f1 <*> transformM f f2
                    FEnv env v f1 f2 ->
                      FEnv <$> mapEnv f env <*> mapVar f v <*> transformM f f1 <*> transformM f f2
                    FList lst -> FList <$> forM lst (transformM f)
                    FSpecial sp -> FSpecial <$> mapSp f sp
  return $ InfoFormula (efm, info)
transformInfoM :: Monad m =>
  (a -> m a')
  -> InfoFormula sp' pop' iop' env' p' v' a
  -> m (InfoFormula sp' pop' iop' env' p' v' a')
transformInfoM f efi = retMapper { mapInfo = f } `transformM` efi

generateInfoM :: Monad f =>
  (InfoFormula sp pop iop env p v a -> f a')
  -> InfoFormula sp pop iop env p v a
  -> f (InfoFormula sp pop iop env p v a')
generateInfoM gen efi@(InfoFormula (ef, _)) = do
  info <- gen efi
  let recall = generateInfoM gen
  efm <- case ef of FPrefix op efi -> FPrefix op <$> recall efi
                    FInfix op ef1 ef2 -> FInfix op <$> recall ef1 <*> recall ef2
                    FEnv env v ef1 ef2 -> FEnv env v <$> recall ef1 <*> recall ef2
                    FList lst -> FList <$> forM lst recall
                    FConst c -> return $ FConst c
                    FVar v -> return $ FVar v
                    FSpecial sp -> return $ FSpecial sp
  return $ InfoFormula (efm, info)

-- | information that can be performed on infix operators
class InfixOperator op where
  isCommutative :: op -> Bool
  isAssociative :: op -> Bool

-- | substitute suitable case with the newly computed term
substitute :: (Monad f) => (InfoFormula sp pop iop env p v a -> Bool)
  -> InfoFormula sp pop iop env p v a
  -> (InfoFormula sp pop iop env p v a -> f (InfoFormula sp pop iop env p v a))
  -> f (InfoFormula sp pop iop env p v a)
substitute test efi compute =
  if test efi then compute efi else
  let recall efi = substitute test efi compute
      InfoFormula (ef, info) = efi
      nef = case ef of
              FPrefix op efi -> FPrefix op <$> recall efi
              FInfix op efi1 efi2 -> FInfix op <$> recall efi1 <*> recall efi2
              FEnv env v efi1 efi2 -> FEnv env v <$> recall efi1 <*> recall efi2
              FList lst -> FList <$> forM lst recall
              v -> return v
  in
  InfoFormula <$> ((,info) <$> nef)

-- fold information attached
instance Foldable (Formula sp pop iop env p v) where
  foldr f init = \case
    FPrefix _ info -> mapInfo info init
    FInfix _ p1 p2 -> foldInfo [p1, p2]
    FEnv _ _ p1 p2 -> foldInfo [p1, p2]
    FList lst      -> foldInfo lst
    v              -> init
    where
      foldInfo = foldr mapInfo init
      mapInfo (InfoFormula (ef, info)) init = f info init `foldrf` ef
      foldrf = foldr f

index :: Num t1 =>
  (t1 -> t2 -> b)  -- ^ given index t1, incorporate it to the original information t2
  -> InfoFormula sp' pop' iop' env' p' v' t2
  -> InfoFormula sp' pop' iop' env' p' v' b
index encode efi =
  runST $ do
  nextIdx <- newSTRef 0
  fun nextIdx `transformInfoM` efi
  where
    fun nextIdx info = do idx <- readSTRef nextIdx
                          writeSTRef nextIdx (idx + 1)
                          return $ encode idx info

unIndex :: (a -> a')  -- ^ the decoding function to extract the index
  -> InfoFormula sp' pop' iop' env' p' v' a
  -> InfoFormula sp' pop' iop' env' p' v' a'
unIndex decode efi = runIdentity $ transformInfoM (return . decode) efi

testQuickCheck :: IO ()
testQuickCheck =
  quickCheck $ withMaxSuccess 20 $ \(info :: InfoFormula () Int Int Int Int Int ()) ->
    trace (show info) True
