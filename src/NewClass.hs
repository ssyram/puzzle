{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
module NewClass where
import qualified Data.Map as Map
import Data.Maybe (listToMaybe)

-- This file defines some new supplementary classes and some of their instances

-- =========================================== IMap ===========================================

class IMap m k v | m -> k, m -> v where
  tryFind :: m -> k -> Maybe v
  insert :: m -> k -> v -> m
  remove :: m -> k -> m
  compute :: m -> k -> (Maybe v -> Maybe v) -> m
  compute map key f = case f $ tryFind map key of
    Nothing -> remove map key
    Just v -> insert map key v
  find :: m -> k -> v 
  find map key = case tryFind map key of
    Nothing -> error "Given key not presented in the map"
    Just v -> v

instance (Ord k) => IMap (Map.Map k v) k v where
  tryFind :: Ord k => Map.Map k v -> k -> Maybe v
  tryFind = (Map.!?)
  insert :: Ord k => Map.Map k v -> k -> v -> Map.Map k v
  insert map key val = Map.insert key val map
  remove :: Ord k => Map.Map k v -> k -> Map.Map k v
  remove map key = Map.delete key map
  find :: Ord k => Map.Map k v -> k -> v
  find = (Map.!)

instance (Eq k) => IMap [(k, v)] k v where
  tryFind :: Eq k => [(k, v)] -> k -> Maybe v
  tryFind lst key = listToMaybe [ v | (k, v) <- lst, k == key ]
  insert :: Eq k => [(k, v)] -> k -> v -> [(k, v)]
  insert lst key val = (key, val) : lst
  remove :: Eq k => [(k, v)] -> k -> [(k, v)]
  remove lst key = [ ele | ele <- lst, fst ele /= key ]
