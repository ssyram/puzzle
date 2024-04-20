-- | DEPRECATED

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

module Equation {-# DEPRECATED "Fatal design problem encountered." #-} where

import Control.Monad.Identity
import Control.Monad.ST.Strict
import Data.Either
import Data.STRef
import Utils
import Data.Maybe

-- Explicitly attach information is a better design as the type transformer should only work as wrapper

-- | info is the information to be attached with the structure of the Formula
data Formula info p v
  = FVar v
  | FConst p
  | FFunc v [(Formula info p v, info)]
  | FAdd (Formula info p v, info) (Formula info p v, info)
  | FMul (Formula info p v, info) (Formula info p v, info)
  | FDiv (Formula info p v, info) (Formula info p v, info)
  | FMinus (Formula info p v, info) (Formula info p v, info)
  | -- | \sum, v is the introduced binding variable
    FSum v (Formula info p v, info) (Formula info p v, info)
  | -- | \prod, v is the introduced binding variable
    FProd v (Formula info p v, info) (Formula info p v, info)

-- | Monad transformer
transformM ::
  Monad m =>
  (t1 -> m info, t2 -> m p, t3 -> m v) ->
  Formula t1 t2 t3 ->
  m (Formula info p v)
transformM helper@(fInfo, fP, fV) =
  let recall f (e1, i1) (e2, i2) = do
        e1 <- transformM helper e1
        i1 <- fInfo i1
        e2 <- transformM helper e2
        i2 <- fInfo i2
        return $ f (e1, i1) (e2, i2)
   in \case
        FVar v -> FVar <$> fV v
        FConst p -> FConst <$> fP p
        FFunc v lst -> do
          let func (e, i) = do e <- transformM helper e
                               i <- fInfo i
                               return (e, i)
          FFunc <$> fV v <*> forM lst func
        FAdd p1 p2 -> recall FAdd p1 p2
        FMul p1 p2 -> recall FMul p1 p2
        FDiv p1 p2 -> recall FDiv p1 p2
        FMinus p1 p2 -> recall FMinus p1 p2
        FSum v p1 p2 -> do
          v <- fV v
          recall (FSum v) p1 p2
        FProd v p1 p2 -> do
          v <- fV v
          recall (FProd v) p1 p2

transform :: (a1 -> info, a2 -> p, a3 -> v) -> Formula a1 a2 a3 -> Formula info p v
transform (fi, fp, fv) t =
  runIdentity $ transformM (return . fi, return . fp, return . fv) t

mapInfoM :: Monad m => (t1 -> m info) -> Formula t1 p v -> m (Formula info p v)
mapInfoM fiM = transformM (fiM, return, return)

mapInfo :: (a1 -> info) -> Formula a1 p v -> Formula info p v
mapInfo fi = transform (fi, id, id)

class s `AddIndex` t where
  addIndex :: Integer -> s -> t
  removeIndex :: t -> s

class ContainsIndex t where getIndex :: t -> Integer

instance (Num t) => AddIndex () t where
  addIndex x _ = fromInteger x
  removeIndex = const ()

index :: AddIndex s info => Formula s p v -> Formula info p v
index f =
  runST $ do
    nextIdx <- newSTRef 0
    mapInfoM (fInfo nextIdx) f
  where
    fInfo nextIdx t = do
      idx <- readSTRef nextIdx
      writeSTRef nextIdx (idx + 1)
      return $ addIndex idx t

unIndex :: AddIndex info t => Formula t p v -> Formula info p v
unIndex = mapInfo removeIndex

newtype FormulaFold p v info = FormulaFold (Formula info p v)

instance Foldable (FormulaFold p v) where
  foldr f init (FormulaFold ef) =
    mapOn ef (const recall) (const init)
    where
      recall (e1, i1) (e2, i2) =
        f i1 $ foldr f (f i2 $ foldr f init $ FormulaFold e2) $ FormulaFold e1

replace ::
  ((Formula info p v, info) -> Bool) ->
  (Formula info p v, info) ->
  (Formula info p v, info) ->
  (Formula info p v, info)
replace test p@(f, info) p' =
  if test p
    then p'
    else mapOn f (\f p1 p2 -> (f (replace test p1 p') (replace test p2 p'), info)) (,info)

-- | get the top level linear form
getLinearForm :: (Formula info p v, info) -> (Char, [(Formula info p v, info)])
getLinearForm p@(ef, info) =
  case ef of
    FAdd {} -> ('+', lvSmooth '+' p)
    FMinus {} -> ('-', lvSmooth '-' p)
    FMul {} -> ('*', lvSmooth '*' p)
    FDiv {} -> ('/', lvSmooth '/' p)
    v -> ('c', [p])
  where
    lvSmooth c p@(ef, info) =
      case c of
        '+' -> case ef of FAdd p1 p2 -> lvSmooth c p1 ++ lvSmooth c p2; _ -> [p]
        '-' -> case ef of FMinus p1 p2 -> lvSmooth c p1 ++ [p2]; _ -> [p]
        '*' -> case ef of FMul p1 p2 -> lvSmooth c p1 ++ lvSmooth c p2; _ -> [p]
        '/' -> case ef of FDiv p1 p2 -> lvSmooth c p1 ++ [p2]; _ -> [p]
        _ -> eIMPOSSIBLE

swapIdx :: ContainsIndex t =>
  Integer -> Integer -> (Formula t p v, t) -> Either [Char] (Formula t p v, t)
swapIdx i i' p =
  -- firstly, avoid having the same index
  if i == i' then return p else do
  (p1, p2) <- parseInfo $ getSwapInfo i i' p
  let infoIs i (_, info) = getIndex info == i
  return $ replace (infoIs i) (replace (infoIs i') p p1) p2
  where
    parseInfo :: Either (Maybe [Char]) b -> Either [Char] b
    parseInfo (Left Nothing) = Left "Indices Not Found"
    parseInfo (Left f) = Left $ fromJust f
    parseInfo (Right r) = Right r

    -- | collect the left and right term if possible, otherwise, return the reason of why cannot
    -- if Left Nothing is returned, this means the indices is not found
    getSwapInfo :: (ContainsIndex t) =>
      Integer -> Integer -> (Formula t p v, t) -> Either (Maybe [Char]) ((Formula t p v, t), (Formula t p v, t))
    getSwapInfo i i' p =
      let (ty, linearLst) = getLinearForm p in
      let idxLst = fmap (\(_, info) -> getIndex info) linearLst in
      case (i `elem` idxLst, i' `elem` idxLst) of
        (True, True) ->
          if (ty == '-' || ty == '/') && (head idxLst == i || head idxLst == i') then
            Left $ return "Context Conflict in '-' or '/'"
          else do
            let func (a, b) p@(_, info)
                  | i == getIndex info = (p, b)
                  | i' == getIndex info = (a, p)
                  | otherwise = (a, b)
            return $ foldl func (undefined, undefined) linearLst
        (False, False) ->
          -- this means we can continue searching lower levels
          let func = \case Left Nothing -> getSwapInfo i i'; x -> const x in
          foldl func (Left Nothing) linearLst
        _              -> Left $ return "Context Conflict"

{-| For environment, the key is just to swap the bounded variable and formula
one key is that the middle environment cannot depend on the latest part
-}
swapEnv i i' p =
  undefined

-- print according to the configuration, which is given by a function of string
class LaTexPrint t where latexPrint :: (String -> String) -> t -> String 
class LaTeXFormatter t where latexFormat :: (String -> String) -> t -> String -> String

-- instance (LaTeXFormatter info, LaTexPrint p, LaTexPrint v) => LaTexPrint (Formula info p v) where
--   latexPrint config ef =
--     case ef of
--       FVar v -> latexPrint config v
--       FConst c -> latexPrint config c
--       FAdd (e1, i1) (e2, i2) ->
--         latexFormat config i1 (latexPrint config e1) ++ " + " ++
--         let modifier = if isSingleOrFunc e2 then id else quoteWith (config "parenStyle") in
--         modifier $ latexFormat config i2 (latexPrint config e2)
--       FMinus (e1, i1) (e2, i2) ->
--         undefined
--     where
--       isSingleOrFunc = \case
--         FVar _ -> True
--         FConst _ -> True 
--         FFunc {} -> True 
--         _ -> False 

  -- analyseResult $ swap i i' p
  -- where
  --   swap i i' p =
  --     let (ty, linearLst) = getLinearForm p
  --      in case ty of
  --           'n' -> (p, False)
  --           '+' ->
  --             let idxLst = fmap (\(_, info) -> getIndex info) linearLst
  --              in case (i `elem` idxLst, i' `elem` idxLst) of
  --                   (True, True) ->
  --                     -- swappable, get swap information and then perform swap on p
  --                     let (l, r) =
  --                           foldr
  --                             ( \(a, b) p@(_, info) ->
  --                                 if i == getIndex info then (p, b) else if i' == getIndex info then (a, p) else (a, b)
  --                             )
  --                             (undefined, undefined)
  --                             linearLst
  --                      in 

-- data SwapResult info p v =
--     SRDone
--   | SRNone
--   | SRPartial (Formula info p v, info) Integer String

-- | The swap function for two environments
--
-- impl note:
--  the key is to find a "join point" where
--  Left means error occured,
--  Right is a pair (term, info), where info is swap found info

-- | SPECIAL NOTE: DO NOT swap environment like Sum or Prod, for these two, use `swapEnv`
-- swapIdx i i' p =
--   analyseResult $ swap i i' p
--   where
--     analyseResult = undefined
--     generateErr str = undefined
--     resultFound = SRDone
--     resultObtained SRDone = True
--     resultObtained _      = False
--     partialResult SRPartial {} = True
--     partialResult _            = False
--     isWithinAdd (SRPartial _ _ mode) = mode == "none" || mode == "+"
--     isWithinAdd _ = eIMPOSSIBLE
--     isWithinMul (SRPartial _ _ mode) = mode == "none" || mode == "*"
--     isWithinMul _ = eIMPOSSIBLE
--     isArg (SRPartial _ _ mode) =
--       case mode of
--         'A' : _ -> True
--         _       -> False
--     isArg _ = eIMPOSSIBLE
--     isHead (SRPartial _ _ mode) =
--       case mode of
--         'H' : _ -> True
--         _       -> False
--     isHead _ = eIMPOSSIBLE
--     conductSwap p (SRPartial p' idx _) =
--       replace (\(_, info) -> idx == getIndex info) p p'
--     conductSwap _ _ = eIMPOSSIBLE
--     getFormula (SRPartial (t, _) _ _) = t
--     getFormula _ = eIMPOSSIBLE
--     unionResult i1 i2 =
--       case (i1, i2) of
--         (SRPartial {}, _) -> i1
--         (_, SRPartial {}) -> i2
--         _                 -> i1  -- both are None here
--     tackleAddMul ::
--       ((Formula info p v, info) -> (Formula info p v, info) -> Formula info p v) ->
--       (Formula info p v, info) -> (Formula info p v, info) -> info -> String ->
--       (SwapResult info p v -> Bool) -> Either String ((Formula info p v, info), SwapResult info p v)
--     tackleAddMul constructor p1 p2 info str isInContext = do
--       (p1, i1) <- swap i i' p1
--       if resultObtained i1 then return ((constructor p1 p2, info), resultFound) else do
--       (p2, i2) <- swap i i' p2
--       if resultObtained i2 then return ((constructor p1 p2, info), resultFound) else do
--       if partialResult i1 && partialResult i2 then
--         if isInContext i1 && isInContext i2 then
--           return ((constructor (conductSwap p1 i2) (conductSwap p2 i1), info), resultFound)
--         else
--           generateErr $
--           "Context Conflict: " ++ showFormula (getFormula i1) ++ " and " ++ showFormula (getFormula i2) ++
--           " is not in the same " ++ quoteWith "``" str ++ " context."
--       else
--         return ((constructor p1 p2, info), unionResult i1 i2)
--     tackleMinusDiv ::
--       ((Formula info p v, info) -> (Formula info p v, info) -> Formula info p v) ->
--       (Formula info p v, info) -> (Formula info p v, info) -> info -> String ->
--       (SwapResult info p v -> Bool) -> String -> Either String ((Formula info p v, info), SwapResult info p v)
--     tackleMinusDiv constructor p1 p2 info str isInContext idStr = do
--       (p1, i1) <- swap i i' p1
--       if resultObtained i1 then return ((constructor p1 p2, info), resultFound) else do
--       (p2, i2) <- swap i i' p2
--       if resultObtained i2 then return ((constructor p1 p2, info), resultFound) else do
--       if partialResult i1 && partialResult i2 then
--         if isInContext i1 && isInContext i2 && isArg i1 && isHead i2 then
--           return ((constructor (conductSwap p1 i2) (conductSwap p2 i1), info), resultFound)
--         else
--           generateErr $
--           "Context Conflict: " ++ showFormula (getFormula i1) ++ " and " ++ showFormula (getFormula i2) ++
--           " is not in the same " ++ quoteWith "``" str ++ " context."
--       else
--         if partialResult i1 then
--           if
--         return ((constructor p1 p2, info), unionResult i1 i2)
--     swap :: Integer -> Integer -> (Formula info p v, info) -> Either String ((Formula info p v, info), SwapResult info p v)
--     swap i i' p@(ef, info)  -- Right means to continue the computation, Left means computation has stoped.
--       | i == getIndex info = return (p, SRPartial p i "none")
--       | i' == getIndex info = return (p, SRPartial p i' "none")
--       | otherwise =
--         case ef of
--           FAdd p1 p2 -> tackleAddMul FAdd p1 p2 info "addition" isWithinAdd
--           FMul p1 p2 -> tackleAddMul FMul p1 p2 info "multiplication" isWithinMul  -- inherit Add
--           FMinus p1 p2 ->
--             let r1 = swap i i' p1 in
--             if resultObtained r1 then propagateResult (`FMinus` p2) else
--             let r2 = swap i i' p2 in
--             if resultObtained r2 then propagateResult $ FMinus p1 else -- it is safe to put p1 here, as result is in p2
--             if partialResult r1 && partialResult r2 then
--               if isArg r1 && isHead r2 then
--                 -- this means both have found and they're valid
--                 conductSwap r1 r2 p
--               else
--                 generateErr $
--                 "Context Conflict: " ++ showFormula (getFormula r1) ++ " and " ++ showFormula (getFormula r2) ++
--                 " is not in the same `minus` context."
--             else
--               unionResult FMinus r1 r2
--           FDiv p1 p2 -> undefined  -- inherit Minus
--           FSum v p1 p2 ->
--             let r1 = swap i i' p1 in
--             if resultObtained r1 then propagateResult (\x -> FSum v x p2) else
--             let r2 = swap i i' p2 in
--             if resultObtained r2 then propagateResult $ FSum v p1 else
--             if partialResult r1 || partialResult r2 then
--               generateErr $
--               "Context Conflict: " ++ showFormula (getFormula r1) ++ " and " ++ showFormula (getFormula r2) ++
--               " is not in the same `addition` context."
--             else
--               unionResult (FSum v) r1 r2
--           FProd v p1 p2 -> undefined  -- inherit FSum
--           v -> notFound

--     -- conductSwap i i' p = do
--     --   (l, r) <- findAndSwap i i' p  -- left means already tackled, just return the result
--     --   if isNothing l || isNothing r then do
--     --     -- this means either left or right index is not found
--     --     l <- analyseByCurrentConfig l p
--     --     r <- analyseByCurrentConfig r p
--     --     return (l, r)
--     --   else
--     --     -- this means we have found the index successfully
--     --     if isValidEnv l r p then

operateWith ::
  (Formula info p v -> (Formula info p v, cont)) ->
  (cont -> info -> info) ->
  Formula info p v ->
  (Formula info p v, cont)
operateWith op infoUpdate f =
  undefined

-- | only parse the non-sum and non-prod part
instance (Read v, Read p) => Read (Formula t v p) where
  readsPrec _ str =
    translate $ parse ([], []) $ lexicalStream lex str
    where
      translate = \case
        Just f -> [(f, "")]
        Nothing -> []

      clearStk :: ([Formula t v p], [String]) -> Maybe ([Formula t v p], [a])
      clearStk (ns, []) = return (ns, [])
      clearStk (n : n' : ns, op : ops) =
        if op /= "(" then clearStk (combines op n' n : ns, ops) else Nothing
      clearStk x = Nothing

      popFstLv :: ([Formula t v p], [String]) -> String -> ([Formula t v p], [String])
      popFstLv (n : n' : ns, "*" : ops) nop = (combines "*" n' n : ns, nop : ops)
      popFstLv (n : n' : ns, "/" : ops) nop = (combines "/" n' n : ns, nop : ops)
      popFstLv (ns, ops) nop = (ns, nop : ops)

      popSndLv :: ([Formula t v p], [String]) -> String -> ([Formula t v p], [String])
      popSndLv (nns@(n : n' : ns), op : ops) nop
        | op `elem` ["*", "/"] = popSndLv (combines op n' n : ns, ops) nop
        | op `elem` ["+", "-"] = (combines op n' n : ns, nop : ops)
        | otherwise = (nns, nop : op : ops)
      popSndLv (ns, ops) nop = (ns, nop : ops)

      popUntilLeft :: ([Formula t v p], [String]) -> Maybe ([Formula t v p], [String])
      popUntilLeft (ns, "(" : ops) = return (ns, ops)
      popUntilLeft (nns@(n : n' : ns), op : ops) = popUntilLeft (combines op n' n : ns, ops)
      popUntilLeft _ = Nothing

      combines :: String -> Formula t v p -> Formula t v p -> Formula t v p
      combines "+" = (. (,undefined)) . FAdd . (,undefined)
      combines "-" = (. (,undefined)) . FMinus . (,undefined)
      combines "*" = (. (,undefined)) . FMul . (,undefined)
      combines "/" = (. (,undefined)) . FDiv . (,undefined)
      combines _ = error "Impossible"

      -- parse :: (Read a) => ([Formula t v p], [String]) -> [String] -> Maybe (Formula t v p)
      parse stks [] = do
        (fStk, syms) <- clearStk stks
        if length fStk == 1 && null syms
          then return $ head fStk
          else Nothing
      parse stks@(fStk, symStk) (x : xs) =
        case x of
          "+" -> parse (popSndLv stks "+") xs
          "-" -> parse (popSndLv stks "-") xs
          "*" -> parse (popFstLv stks "*") xs
          "/" -> parse (popFstLv stks "/") xs
          "(" -> parse (fStk, "(" : symStk) xs
          ")" -> popUntilLeft stks >>= (`parse` xs)
          val ->
            -- firstly, try parsing a number, of type p
            let lst = readsPrec 1 val
             in if not $ null lst
                  then parse (FConst (fst $ head lst) : fStk, symStk) xs
                  else -- then, try parsing any other kinds of type v

                    let lst = readsPrec 1 val
                     in if null lst
                          then Nothing
                          else parse (FVar (fst $ head lst) : fStk, symStk) xs

showFormula :: (Show p, Show a) => Formula b p a -> String
showFormula ef =
  let printSndLv e' =
        let e = extract e'
         in case e of
              FAdd _ _ -> addBrkt e
              FMinus _ _ -> addBrkt e
              _ -> showFormula e
   in case ef of
        FVar a -> show a
        FConst c -> show c
        FAdd e1 e2 -> showFormula (extract e1) ++ " + " ++ showFormula (extract e2)
        FFunc v eLst -> show v -- ++ quoteWith "()" (showFormula $ extract e)
        FMinus e1 e2 ->
          showFormula (extract e1) ++ " - "
            ++ case extract e2 of FMinus _ _ -> addBrkt (extract e2); _ -> showFormula (extract e2)
        FMul e1 e2 ->
          printSndLv e1 ++ " * " ++ printSndLv e2
        FDiv e1 e2 ->
          printSndLv e1 ++ " / "
            ++ case extract e2 of
              FVar a -> show a
              FMul _ _ -> showFormula (extract e2)
              _ -> addBrkt (extract e2)
        FSum v e1 e2 ->
          "\\sum_{" ++ show v ++ " \\in "
            ++ quoteWith "{}" (showFormula $ extract e1)
            ++ "}"
            ++ quoteWith "()" (showFormula $ extract e2)
        FProd v e1 e2 ->
          "\\prod_{" ++ show v ++ " \\in "
            ++ quoteWith "{}" (showFormula $ extract e1)
            ++ "}"
            ++ quoteWith "()" (showFormula $ extract e2)
  where
    addBrkt = quoteWith "()" . showFormula
    extract = fst

instance (Show v, Show p) => Show (Formula t v p) where
  show ef =
    let printSndLv e' =
          let e = extract e'
           in case e of
                FAdd _ _ -> addBrkt e
                FMinus _ _ -> addBrkt e
                _ -> show e
     in case ef of
          FVar a -> show a
          FConst c -> show c
          FFunc v e -> show v  -- ++ quoteWith "()" (show $ extract e)
          FAdd e1 e2 -> show (extract e1) ++ " + " ++ show (extract e2)
          FMinus e1 e2 ->
            show (extract e1) ++ " - "
              ++ case extract e2 of FMinus _ _ -> addBrkt (extract e2); _ -> show (extract e2)
          FMul e1 e2 ->
            printSndLv e1 ++ " * " ++ printSndLv e2
          FDiv e1 e2 ->
            printSndLv e1 ++ " / "
              ++ case extract e2 of
                FVar a -> show a
                FMul _ _ -> show (extract e2)
                _ -> addBrkt (extract e2)
          FSum v e1 e2 ->
            "\\sum_{" ++ show v ++ " \\in "
              ++ quoteWith "{}" (show $ extract e1)
              ++ "}"
              ++ quoteWith "()" (show $ extract e2)
          FProd v e1 e2 ->
            "\\prod_{" ++ show v ++ " \\in "
              ++ quoteWith "{}" (show $ extract e1)
              ++ "}"
              ++ quoteWith "()" (show $ extract e2)
    where
      addBrkt = quoteWith "()" . show
      extract = fst

-- opOnIdx :: (Wrapper t info, Eq info) =>
--   info
--   -> (Formula (IndexedType info) p1 v -> Formula t p2 v -> Formula t p2 v)
--   -> IndexedType info (Formula (IndexedType info) p1 v)
--   -> Formula t p2 v
--   -> t (Formula t p2 v)
-- opOnIdx tIdx op (IndexedType (idx, f)) =
--   if tIdx == idx
--     then do t <- op f; return $ enclose idx t
--     else mapOn recall (return $ enclose idx) f
--   where
--     recall f t1 t2 = do
--       t1 <- opOnIdx tIdx op t1
--       t2 <- opOnIdx tIdx op t2
--       return $ enclose idx $ f t1 t2

mapOn f recall baseCall = case f of
  FAdd f1 f2 -> recall FAdd f1 f2
  FMul f1 f2 -> recall FMul f1 f2
  FDiv f1 f2 -> recall FDiv f1 f2
  FMinus f1 f2 -> recall FMinus f1 f2
  FSum v f1 f2 -> recall (FSum v) f1 f2
  FProd v f1 f2 -> recall (FProd v) f1 f2
  v -> baseCall v
