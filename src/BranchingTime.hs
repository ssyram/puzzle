{-# LANGUAGE GADTs #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant flip" #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
module BranchingTime where
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.List as List
import Prelude hiding ((&&), (||), not)
import qualified Prelude
import Utils
import Data.Maybe
import Control.Monad.Reader (Reader)

data Operation q m g sp
  = OpUp q m g
  | OpDown q m
  | OpSp sp

data RestrictedPTSA q m g p sp =
  RestrictedPTSA {
    restriction :: Int,
    states :: Set.Set q,
    locMem :: Set.Set m,
    gammas :: Set.Set g,
    rules :: Map.Map (q, m, g) [(q, Operation q m g sp)],
    initState :: q,
    defaultLocMem :: m,
    botGamma :: g
  }

data DetRabinAut d s
  = DetRabinAut {
    draStates :: Set.Set d,
    draSigmas :: Set.Set s,
    draRules :: Map.Map (d, s) d,
    draInitState :: d
  }

revDRARules :: (Ord a, Ord b) => DetRabinAut a b -> Map.Map (a, b) (Set.Set a)
revDRARules dra =
  draRules dra
  |> Map.toList
  |> fmap (\((d, s), d') -> ((d', s), d))
  |> flip foldl Map.empty (\map ((d', s), d) -> Map.alter (addMap d) (d', s) map)
  where
    addMap :: Ord a => a -> Maybe (Set.Set a) -> Maybe (Set.Set a)
    addMap d maybeSet =
      Just $ Set.insert d $ fromMaybe Set.empty maybeSet

-- Var_D^g
data Var q g = Var { downList :: [q], gamma :: g }

data Direction g
  = Up g
  | Down
  deriving (Eq)

-- | (q, q', m, \kappa)
newtype InteractionUnit q m g = InteractionUnit (q, q, m, Direction g)

data SynPath q m g = SynPath [InteractionUnit q m g] g

synPathToVar :: Eq g => SynPath q m g -> Var q g
synPathToVar (SynPath path g) =
  Var [ q | InteractionUnit (q, _, _, dir) <- path, dir == Down ] g

class StateTag src tag status | src -> status where
  -- | to compute backwardly the value
  backTrack :: src -> status -> tag -> tag
  allTags :: src -> [tag]

instance (Ord d, Ord s) => StateTag (DetRabinAut d s) [d] s where
  backTrack :: (Ord d, Ord s) => DetRabinAut d s -> s -> [d] -> [d]
  backTrack dra s lst =
    let set = Set.fromList lst in
    [ d |
      d <- Set.toList $ draStates dra,
      maybe False (`Set.member` set) $ draRules dra Map.!? (d, s)
    ]
  allTags :: (Ord d, Ord s) => DetRabinAut d s -> [[d]]
  allTags = getAllTags
    where
      getAllTags :: (Ord d, Ord s) => DetRabinAut d s -> [[d]]
      getAllTags dra =
        draStates dra
        |> Set.toList
        |> allCombinations

instance (Ord d, Ord s) => StateTag (DetRabinAut d s) (Set.Set d) s where
  backTrack :: (Ord d, Ord s) => DetRabinAut d s -> s -> Set.Set d -> Set.Set d
  backTrack dra s set =
    Set.fromList [ d |
      d <- Set.toList $ draStates dra,
      maybe False (`Set.member` set) $ draRules dra Map.!? (d, s)
    ]
  allTags :: (Ord d, Ord s) => DetRabinAut d s -> [Set.Set d]
  allTags = getAllTags
    where
      getAllTags :: (Ord d, Ord s) => DetRabinAut d s -> [Set.Set d]
      getAllTags dra =
        draStates dra
        |> Set.toList
        |> allCombinations
        |> fmap Set.fromList

data LinearTimeLogic a
  = LTLAtom a
  | LTLTrue
  | LTLFalse
  | LTLNot (LinearTimeLogic a)
  | LTLAnd (LinearTimeLogic a) (LinearTimeLogic a)
  | LTLNext (LinearTimeLogic a)
  | LTLUntil (LinearTimeLogic a) (LinearTimeLogic a)
  deriving (Show, Ord, Eq)

-- | The class of propositional logic
class PropLogic t where
  true :: t
  false :: t
  (&&) :: t -> t -> t
  not :: t -> t
  (||) :: t -> t -> t

instance PropLogic (LinearTimeLogic a) where
  true :: LinearTimeLogic a
  true = LTLTrue
  false :: LinearTimeLogic a
  false = LTLFalse
  (&&) :: LinearTimeLogic a -> LinearTimeLogic a -> LinearTimeLogic a
  (&&) = LTLAnd
  not :: LinearTimeLogic a -> LinearTimeLogic a
  not = LTLNot
  (||) :: LinearTimeLogic a -> LinearTimeLogic a -> LinearTimeLogic a
  ltl || ltl' = LTLNot $ LTLNot ltl `LTLAnd` LTLNot ltl'

instance PropLogic Bool where
  true :: Bool
  true = True
  false :: Bool
  false = False
  (&&) :: Bool -> Bool -> Bool
  (&&) = (Prelude.&&)
  not :: Bool -> Bool
  not = Prelude.not
  (||) :: Bool -> Bool -> Bool
  (||) = (Prelude.||)

infixr 3 &&
infixr 2 ||

newtype LTLType a = LTLType (Set.Set (LinearTimeLogic a))
  deriving (Eq, Ord, Show)

subLTLFormulas :: (Ord a) => LinearTimeLogic a -> Set.Set (LinearTimeLogic a)
subLTLFormulas ori@(LTLNot ltl') = Set.insert ori $ subLTLFormulas ltl'
subLTLFormulas ori@(LTLAnd ltl' ltl_a) =
  Set.insert ori $ subLTLFormulas ltl' `Set.union` subLTLFormulas ltl_a
subLTLFormulas ori@(LTLNext ltl') = Set.insert ori $ subLTLFormulas ltl'
subLTLFormulas ori@(LTLUntil ltl' ltl_a) =
  Set.insert ori $ subLTLFormulas ltl' `Set.union` subLTLFormulas ltl_a
subLTLFormulas atom = Set.insert atom Set.empty

type Valuation s a = s -> Set.Set a

data AutLTLContext q m g a =
  AutLTLContext {
    ctxFormula :: LinearTimeLogic a,
    ctxValuation :: Valuation (q, m, g) a,
    ctxM0 :: m
  }

allLTLTypes :: Ord a => LinearTimeLogic a -> [LTLType a]
allLTLTypes formula =
  subLTLFormulas formula
  |> Set.toList
  |> allCombinations
  |> fmap (LTLType . Set.fromList)

backwardDet :: Ord a => AutLTLContext q m g a -> (q, m, g) -> LTLType a -> LTLType a
backwardDet ctx s oldType =
  LTLType $ Set.fromList [ f |
    f <- Set.toList $ subLTLFormulas $ ctxFormula ctx, 
    satisfy (ctxValuation ctx) s oldType f
  ]
  where
    satisfy :: (Ord a) => Valuation s a -> s -> LTLType a -> LinearTimeLogic a -> Bool
    satisfy val s _ (LTLAtom a) = a `Set.member` val s
    satisfy _ _ _ LTLTrue = true
    satisfy _ _ _ LTLFalse = false
    satisfy val s oldType (LTLNot ltl) = not $ satisfy val s oldType ltl
    satisfy val s oldType (LTLAnd ltl ltl') =
      satisfy val s oldType ltl && satisfy val s oldType ltl'
    satisfy _ _ (LTLType oldSet) (LTLNext ltl) = ltl `Set.member` oldSet
    satisfy val s oldType@(LTLType oldSet) f@(LTLUntil ltl ltl') =
      satisfy val s oldType ltl' || f `Set.member` oldSet && satisfy val s oldType ltl

ltlTagSynPath :: Ord a =>
  AutLTLContext q m g a
  -> SynPath q m g
  -> [SynPath (q, LTLType a) m g]
ltlTagSynPath ctx (SynPath path g) =
  fullQual (ctxM0 ctx) path
  |> fmap (performTag ctx g)
  |> cartesianProduct
  |> fmap (`SynPath` g)
  where
    fullQual :: Foldable t =>
      m -> t (InteractionUnit q m g) -> [(m, InteractionUnit q m g)]
    fullQual m0 path = snd $ foldl (\(mp, lst) unit@(InteractionUnit (_, _, m, _)) ->
      (m, (mp, unit) : lst)) (m0, []) path
    performTag :: Ord a =>
      AutLTLContext q m g a
      -> g
      -> (m, InteractionUnit q m g)
      -> [InteractionUnit (q, LTLType a) m g]
    performTag ctx g pair =
      allLTLTypes (ctxFormula ctx)
      |> fmap (addInferType ctx pair g)
    addInferType :: Ord a =>
      AutLTLContext q m g a
      -> (m, InteractionUnit q m g)
      -> g
      -> LTLType a
      -> InteractionUnit (q, LTLType a) m g
    addInferType ctx (mp, InteractionUnit (q, q', m, kappa)) g ty =
      InteractionUnit (
        (q, backwardDet ctx (q, mp, g) ty),
        (q', ty),
        m,
        kappa
      )
