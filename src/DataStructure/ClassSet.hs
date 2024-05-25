{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module DataStructure.ClassSet where
import qualified Data.Set as S
import Utils (eIMPOSSIBLE)

class ISet s where
  type Element s
  emptySet :: s
  addToSet :: s -> Element s -> s
  inSet :: s -> Element s -> Bool
  removeFromSet :: s -> Element s -> s
  sizeSet :: Integral i => s -> i

class Check x where
  check :: x -> x

instance Ord x => ISet (S.Set x) where
  type Element (S.Set x) = x
  emptySet :: Ord x => S.Set x
  emptySet = S.empty
  addToSet :: Ord x => S.Set x -> Element (S.Set x) -> S.Set x
  addToSet = flip S.insert
  inSet :: Ord x => S.Set x -> Element (S.Set x) -> Bool
  inSet = flip S.member
  removeFromSet :: Ord x => S.Set x -> Element (S.Set x) -> S.Set x
  removeFromSet = flip S.delete
  sizeSet :: (Ord x, Integral i) => S.Set x -> i
  sizeSet = fromIntegral . S.size

instance Check (S.Set x) where
  check :: S.Set x -> S.Set x
  check = id

listSetOperations :: (Foldable t, Integral a, Check b, ISet b) => b -> t (a, Element b) -> [Bool]
listSetOperations empty lst = fst $ foldl folder ([], empty) lst
  where
    folder (acc, set) (opCode, el) =
      case abs $ opCode `mod` 3 of
        -- add
        0 -> (acc, check $ addToSet set el)
        -- delete
        1 -> (acc, check $ removeFromSet set el)
        -- search
        2 -> (inSet set el:acc, set)
        _ -> eIMPOSSIBLE

testSet :: (Check b, ISet b, Element b ~ Int) => b -> [(Int, Int)] -> Bool
testSet empty (l :: [(Int, Int)]) =
  listSetOperations S.empty l == listSetOperations empty l
