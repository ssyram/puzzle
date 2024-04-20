{-# LANGUAGE Strict #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module ExprParser where

import Text.Parsec
import Text.Parsec.String (Parser)
import Text.Parsec.Language (emptyDef)
import Text.Parsec.Expr
import qualified Text.Parsec.Token as T
import Debug.Trace (trace)
import qualified Data.Set as Set
import Utils (concatStr)

lexer = T.makeTokenParser emptyDef

parens = T.parens lexer
integer = T.integer lexer
identifier = T.identifier lexer
whiteSpace = T.whiteSpace lexer
reservedOp = T.reservedOp lexer
reserved = T.reserved lexer

data ArithExpr v t =
    AConst t
  | AVar v
  | AAdd (ArithExpr v t) (ArithExpr v t)
  | AMinus (ArithExpr v t) (ArithExpr v t)
  | AMul (ArithExpr v t) (ArithExpr v t)
  deriving Show

data CmpOp =
    CLe
  | CLt
  | CEq
  | CNeq
  | CGt
  | CGe
  deriving Show

data BoolExpr v t =
    BTrue
  | BFalse
  | BAnd (BoolExpr v t) (BoolExpr v t)
  | BOr (BoolExpr v t) (BoolExpr v t)
  | BNot (BoolExpr v t)
  | BCmp CmpOp (ArithExpr v t) (ArithExpr v t)
  deriving Show

-- parse variables in arith expr
parseAVar :: Parser (ArithExpr String Integer)
parseAVar = do
  v <- identifier
  return $ AVar v

parseAConst :: Parser (ArithExpr String Integer)
parseAConst = do
  n <- integer
  return $ AConst (fromIntegral n)

parseANeg :: Parser (ArithExpr String Integer)
parseANeg = do
  reservedOp "-"
  AMinus (AConst 0) <$> parseArithExpr

parseArithTerm :: Parser (ArithExpr String Integer)
parseArithTerm = parseAVar <|> parseAConst <|> parens parseArithExpr <|> parseANeg

parseArithExpr :: Parser (ArithExpr String Integer)
parseArithExpr = buildExpressionParser
  [ [ Infix (reservedOp "*" >> return AMul) AssocLeft ]
  , [ Infix (reservedOp "+" >> return AAdd) AssocLeft
    , Infix (reservedOp "-" >> return AMinus) AssocLeft ]
  ] parseArithTerm

parseCmpOp :: Parser CmpOp
parseCmpOp = (reservedOp ">=" >> return CGe)
          <|> (reservedOp "<=" >> return CLe)
          <|> (reservedOp "<" >> return CLt)
          <|> (reservedOp ">" >> return CGt)
          <|> (reservedOp "==" >> return CEq)
          <|> (reservedOp "!=" >> return CNeq)

parseBoolTerm :: Parser (BoolExpr String Integer)
parseBoolTerm = (reserved "true" >> return BTrue)
             <|> (reserved "false" >> return BFalse)
             <|> parseNeg
             <|> try parseCmp
             <|> parens parseBoolExpr

parseCmp :: Parser (BoolExpr String Integer)
parseCmp = do
  a1 <- parseArithExpr
  op <- parseCmpOp
  BCmp op a1 <$> parseArithExpr

parseNeg :: Parser (BoolExpr String Integer)
parseNeg = do
  reservedOp "!"
  BNot <$> parseBoolExpr

parseBoolExpr :: Parser (BoolExpr String Integer)
parseBoolExpr = buildExpressionParser
  [ [ Prefix (reservedOp "!" >> return BNot) ]
  , [ Infix (reservedOp "&" >> return BAnd) AssocLeft ]
  , [ Infix (reservedOp "|" >> return BOr) AssocLeft ]
  ] parseBoolTerm

parseExpression :: Parser (BoolExpr String Integer)
parseExpression = do
  whiteSpace
  b <- parseBoolExpr
  eof
  return b

-- >>> fmap toSMTLIB haveATry
-- Right "(and (and (and (and (and (and (>= (+ A (- 1)) 0) (>= (+ B (- 1)) 0)) (>= (+ C (- 1)) 0)) (or (or (not (>= (+ (+ (+ A (- 1)) 3) (- 1)) 0)) (not (>= (+ (+ B (- 1)) (- 1)) 0))) (not (>= (+ (+ C (- 1)) (- 1)) 0)))) (not (>= (+ (+ 1 (* (- 1) (+ (+ B A) C))) (- 1)) 0))) (or (or (not (>= (+ (+ A (- 1)) (- 1)) 0)) (not (>= (+ (+ (+ B (- 1)) 3) (- 1)) 0))) (not (>= (+ (+ C (- 1)) (- 1)) 0)))) (or (or (not (>= (+ (+ A (- 1)) (- 1)) 0)) (not (>= (+ (+ B (- 1)) (- 1)) 0))) (not (>= (+ (+ (+ C (- 1)) 3) (- 1)) 0))))"
haveATry :: Either ParseError (BoolExpr String Integer)
haveATry = parse parseExpression "Try" "((((((((A + -1) >= 0) & ((B + -1) >= 0)) & ((C + -1) >= 0)) & ((!((((A + -1) + 3) + -1) >= 0) | !(((B + -1) + -1) >= 0)) | !(((C + -1) + -1) >= 0))) & !(((1 + -1 * ((B + A) + C)) + -1) >= 0)) & ((!(((A + -1) + -1) >= 0) | !((((B + -1) + 3) + -1) >= 0)) | !(((C + -1) + -1) >= 0))) & ((!(((A + -1) + -1) >= 0) | !(((B + -1) + -1) >= 0)) | !((((C + -1) + 3) + -1) >= 0)))"

parseToBoolExpr :: String -> Either ParseError (BoolExpr String Integer)
parseToBoolExpr = parse parseExpression "parse"

translateToSMTLIB :: String -> Either ParseError String
translateToSMTLIB = fmap toSMTLIB . parse parseExpression "trans"

translateToSMTLIBQuery :: String -> String
translateToSMTLIBQuery str =
  let res = parseToBoolExpr str in
  case res of
    Right expr ->
      let vars = collectVars expr in
      concatStr "\n" $ 
        [ "(declare-const " ++ var ++ " Int)" | var <- vars ] ++
        [ "\n" ] ++
        [ "(assert " ++ toSMTLIB expr ++ ")" ] ++
        [ "\n" ] ++
        [ "(check-sat)" ] ++
        [ "\n" ] ++
        [ "(get-model)" ]
    Left err -> error $ show err

class ColVar t v | t -> v where
  collectVarsSet :: t -> Set.Set v
  collectVars :: t -> [v]
  collectVars = Set.toList . collectVarsSet

instance Ord v => ColVar (ArithExpr v t) v where
  collectVarsSet :: (Ord v) => ArithExpr v t -> Set.Set v
  collectVarsSet (AConst _) = Set.empty
  collectVarsSet (AVar v) = Set.insert v Set.empty
  collectVarsSet (AAdd a1 a2)
    = let
        ae_c = collectVarsSet a1
        a2_c = collectVarsSet a2
      in Set.union ae_c a2_c
  collectVarsSet (AMinus a1 a2)
    = let
        ae_c = collectVarsSet a1
        a2_c = collectVarsSet a2
      in Set.union ae_c a2_c
  collectVarsSet (AMul a1 a2)
    = let
        ae_c = collectVarsSet a1
        a2_c = collectVarsSet a2
      in Set.union ae_c a2_c

instance Ord v => ColVar (BoolExpr v t) v where
  collectVarsSet :: Ord v => BoolExpr v t -> Set.Set v
  collectVarsSet BTrue = Set.empty
  collectVarsSet BFalse = Set.empty
  collectVarsSet (BAnd b1 b2)
    = let
        b1' = collectVarsSet b1
        b2' = collectVarsSet b2
      in Set.union b1' b2'
  collectVarsSet (BOr b1 b2)
    = let
        b1' = collectVarsSet b1
        b2' = collectVarsSet b2
      in Set.union b1' b2'
  collectVarsSet (BNot b1) = collectVarsSet b1
  collectVarsSet (BCmp _ a1 a2)
    = let
        a1' = collectVarsSet a1
        a2' = collectVarsSet a2
      in Set.union a1' a2'

class Simplifiable t where
  simplify :: (Num n, Ord n) => t n -> t n

instance Simplifiable (ArithExpr v) where
  simplify :: (Num n, Ord n) => ArithExpr v n -> ArithExpr v n
  simplify (AConst n) = AConst n
  simplify (AVar v) = AVar v
  simplify (AAdd a1 a2)
    = let
        a1' = simplify a1
        a2' = simplify a2
      in case (a1', a2') of
        (AConst c1, AConst c2) -> AConst $ c1 + c2
        (_, _) -> AAdd a1' a2'
  simplify (AMinus a1 a2)
    = let
        a1' = simplify a1
        a2' = simplify a2
      in case (a1', a2') of
        (AConst c1, AConst c2) -> AConst $ c1 - c2
        (_, _) -> AMinus a1' a2'
  simplify (AMul a1 a2)
    = let
        a1' = simplify a1
        a2' = simplify a2
      in case (a1', a2') of
        (AConst c1, AConst c2) -> AConst $ c1 * c2
        (_, _) -> AMul a1' a2'

boolToBoolExpr :: Bool -> BoolExpr v t
boolToBoolExpr False = BFalse
boolToBoolExpr True = BTrue

instance Simplifiable (BoolExpr v) where
  simplify :: (Num n, Ord n) => BoolExpr v n -> BoolExpr v n
  simplify BTrue = BTrue
  simplify BFalse = BFalse
  simplify (BAnd b1 b2)
    = let
        b1' = simplify b1
        b2' = simplify b2
      in case (b1', b2') of
        (BTrue, _) -> b2'
        (_, BTrue) -> b1'
        (BFalse, _) -> BFalse
        (_, BFalse) -> BFalse
        (b1', b2') -> BAnd b1' b2'
  simplify (BOr b1 b2)
    = let
        b1' = simplify b1
        b2' = simplify b2
      in case (b1', b2') of
        (BTrue, _) -> BTrue
        (_, BTrue) -> BTrue
        (BFalse, _) -> b2'
        (_, BFalse) -> b1'
        (b1', b2') -> BOr b1' b2'
  simplify (BNot b1) = let b1' = simplify b1 in case b1' of
                         BTrue -> BFalse
                         BFalse -> BTrue
                         _ -> BNot b1'
  simplify (BCmp op a1 a2)
    = let
        a1' = simplify a1
        a2' = simplify a2
      in case (a1', a2') of
        (AConst c1, AConst c2) -> boolToBoolExpr $ case op of
          CLe -> c1 <= c2
          CLt -> c1 < c2
          CEq -> c1 == c2
          CNeq -> c1 /= c2
          CGt -> c1 >= c2
          CGe -> c1 > c2
        (_, _) -> BCmp op a1' a2'

class ToSMTLIB t where
    toSMTLIB :: t -> String

instance ToSMTLIB Integer where
    toSMTLIB :: Integer -> String
    toSMTLIB = show

instance ToSMTLIB String where
    toSMTLIB :: String -> String
    toSMTLIB = id

instance (ToSMTLIB v, ToSMTLIB t, Num t, Ord t) => ToSMTLIB (ArithExpr v t) where
    toSMTLIB :: (ToSMTLIB v, ToSMTLIB t, Num t, Ord t) => ArithExpr v t -> String
    toSMTLIB (AConst t) = if t < 0 then "(- " ++ toSMTLIB (abs t) ++ ")" else toSMTLIB t
    toSMTLIB (AVar v) = toSMTLIB v
    toSMTLIB (AAdd e1 e2) = "(+ " ++ toSMTLIB e1 ++ " " ++ toSMTLIB e2 ++ ")"
    toSMTLIB (AMinus e1 e2) = "(- " ++ toSMTLIB e1 ++ " " ++ toSMTLIB e2 ++ ")"
    toSMTLIB (AMul e1 e2) = "(* " ++ toSMTLIB e1 ++ " " ++ toSMTLIB e2 ++ ")"

instance ToSMTLIB CmpOp where
    toSMTLIB :: CmpOp -> String
    toSMTLIB CLe = "<="
    toSMTLIB CLt = "<"
    toSMTLIB CEq = "="
    toSMTLIB CNeq = "distinct"
    toSMTLIB CGt = ">"
    toSMTLIB CGe = ">="

instance (ToSMTLIB v, ToSMTLIB t, Num t, Ord t) => ToSMTLIB (BoolExpr v t) where
    toSMTLIB :: (ToSMTLIB v, ToSMTLIB t, Num t, Ord t) => BoolExpr v t -> String
    toSMTLIB BTrue = "true"
    toSMTLIB BFalse = "false"
    toSMTLIB (BAnd b1 b2) = "(and " ++ toSMTLIB b1 ++ " " ++ toSMTLIB b2 ++ ")"
    toSMTLIB (BOr b1 b2) = "(or " ++ toSMTLIB b1 ++ " " ++ toSMTLIB b2 ++ ")"
    toSMTLIB (BNot b) = "(not " ++ toSMTLIB b ++ ")"
    toSMTLIB (BCmp op e1 e2) = "(" ++ toSMTLIB op ++ " " ++ toSMTLIB e1 ++ " " ++ toSMTLIB e2 ++ ")"


-- class ConstComb t where
--   combineConst :: (Num n) => t n -> t n

-- instance ConstComb (ArithExpr v) where
--   combineConst :: Num n => ArithExpr v n -> ArithExpr v n
--   combineConst (AConst n) = AConst n
--   combineConst (AVar v) = AVar v
--   combineConst (AAdd a1 a2)
--     = let
--         a1_c = combineConst a1
--         a2' = combineConst a2
--       in case (a1', a2') of
--   combineConst (AMinus a1 a2)
--     = let
--         a1_c = combineConst a1
--         a2' = combineConst a2
--       in case (a1', a2') of
--   combineConst (AMul a1 a2)
--     = let
--         a1_c = combineConst a1
--         a2' = combineConst a2
--       in case (a1', a2') of
--   combineConst (ADiv a1 a2)
--     = let
--         a1_c = combineConst a1
--         a2' = combineConst a2
--       in case (a1', a2') of

-- instance ConstComb (BoolExpr v) where
--   combineConst :: Num n => BoolExpr v n -> BoolExpr v n
--   combineConst BTrue = BTrue
--   combineConst BFalse = BFalse
--   combineConst (BAnd b1 b2)
--     = let
--         b1' = combineConst b1
--         b2' = combineConst b2
--       in _w5iW
--   combineConst (BOr b1 b2)
--     = let
--         b1' = combineConst b1
--         b2' = combineConst b2
--       in _w5iX
--   combineConst (BNot b1) = let b1' = combineConst b1 in _w5iY
--   combineConst (BCmp op a1 a2)
--     = let
--         a1' = combineConst a1
--         a2' = combineConst a2
--       in _w5iZ
