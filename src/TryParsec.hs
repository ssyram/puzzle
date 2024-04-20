{-# LANGUAGE StrictData #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstrainedClassMethods #-}
module TryParsec where
import Text.Parsec as Parsec
import Text.Parsec.String (Parser)
import Text.Parsec.Language (emptyDef)
import Text.Parsec.Token
import Control.Applicative ((<*), (*>), (<$>), (<*>))
import Data.Ratio ((%))
import Text.Read (readEither, choice, ReadPrec)
import qualified GHC.Read as Read
import Text.ParserCombinators.ReadPrec
import Text.ParserCombinators.ReadP (ReadP, readS_to_P, choice)
import Utils (quoteWith, printSeq, concatStr, eIMPOSSIBLE)
import Data.Char (isDigit, isSpace)
import Control.Monad (void)
import Data.Functor

import Dummy

data Expr
  = EVar !String
  | EConst !Rational
  | EAdd !Expr !Expr
  | EMul !Expr !Expr
  deriving (Show)

lexer :: TokenParser ()
lexer = makeTokenParser emptyDef
  { identStart = letter <|> char '_'
  , identLetter = alphaNum <|> char '_'
  , opStart = oneOf "+*"
  , opLetter = oneOf "+*"
  }

inParens :: Parser a -> Parser a
inParens = parens lexer
getIdentifier :: Parser String
getIdentifier = identifier lexer
getReservedOp :: String -> Parser ()
getReservedOp = reservedOp lexer
getWhiteSpace = whiteSpace lexer
getInteger = integer lexer

rational :: Parser Rational
rational = do
  num <- fromInteger <$> getInteger
  char '/'
  denom <- fromInteger <$> getInteger
  return (num % denom)

constant :: Parser Expr
constant = EConst <$> (try rational <|> (fromInteger <$> getInteger))

variable :: Parser Expr
variable = EVar <$> getIdentifier

atom :: Parser Expr
atom = inParens expression <|> try constant <|> variable

term :: Parser Expr
term = chainl1 atom (getReservedOp "*" >> return EMul)

expression :: Parser Expr
expression = chainl1 term (getReservedOp "+" >> return EAdd)

-- >>> parseExpr "x + 3 * (y + 1/2)"
-- Right (EAdd (EVar "x") (EMul (EConst (3 % 1)) (EAdd (EVar "y") (EConst (1 % 2)))))
parseExpr :: String -> Either ParseError Expr
parseExpr = parse (getWhiteSpace *> expression <* eof) "expression"


testMain :: IO ()
testMain = do
  let input = "x + 3 * (y + 1/2)"
  case parseExpr input of
    Left err -> putStrLn $ "Error: " ++ show err
    Right expr -> putStrLn $ "Parsed expression: " ++ show expr


data SExpr d
  = SNode !d ![SExpr d]
  | SList ![SExpr d]
  -- deriving (Show)

-- | to show the internal information -- because the out-most `(x)` show be printed as `(x)`
--   rather than pure `x`
showInternal :: Show a => SExpr a -> String
showInternal (SList lst) = quoteWith "()" $ concatStr " " $ fmap showInternal lst
showInternal (SNode hd []) = show hd
showInternal (SNode hd lst) =
  quoteWith "()" $ show hd ++ " " ++ concatStr " " (fmap showInternal lst)

instance Show d => Show (SExpr d) where
  show :: Show d => SExpr d -> String
  show expr =
    case expr of
      SNode x [] -> quoteWith "()" $ show x
      _anyOther  -> showInternal expr


getNumStr :: Parser String
getNumStr = do
  sign <- option "" $ string "-" <|> string "+"
  intPart <- many1 digit
  fracPart <- option "" $ do
    dot <- char '.'
    fracDigits <- many1 digit
    return $ dot : fracDigits
  expPart <- option "" $ do
    e <- oneOf "eE"
    expSign <- option "" $ string "-" <|> string "+"
    expDigits <- many1 digit
    return $ e : expSign ++ expDigits
  return $ sign ++ intPart ++ fracPart ++ expPart

getOperator :: Parser String
getOperator = many1 $ oneOf "+-*/~!#$%^|&@=<>"

getSingleElement :: Parser String
getSingleElement =
  Parsec.choice [
    try getNumStr,
    try getIdentifier,
    try getOperator
  ]

getNode :: (Read d) => Parser (SExpr d)
getNode = do
  getWhiteSpace
  content <- getSingleElement
  getWhiteSpace
  info <- many getSExpr
  getWhiteSpace
  case readEither content of
    Right lbl -> return $ SNode lbl info
    Left  msg -> fail msg

getList :: (Read d) => Parser (SExpr d)
getList = fmap SList $ many $ getWhiteSpace *> getSExpr

getSingleNode :: (Read d) => Parser (SExpr d)
getSingleNode = do
  getWhiteSpace
  content <- getSingleElement
  getWhiteSpace
  case readEither content of
    Right lbl -> return $ SNode lbl []
    Left  msg -> fail msg

getSExpr :: (Read d) => Parser (SExpr d)
getSExpr = getSingleNode <|> inParens (getNode <|> getList)

parseSExpr :: (Read d) => String -> Either ParseError (SExpr d)
parseSExpr = parse (getWhiteSpace *> getSExpr <* eof) "SExpr"


instance (Read d) => Read (SExpr d) where
  readPrec :: Read d => ReadPrec (SExpr d)
  readPrec = do
    -- the trick to extract the actual input string out
    str <- lift $ readS_to_P (\s -> [ (s, "") ])
    case parseSExpr str of
      Right val -> return val
      Left  err -> fail $ show err
  -- A different function to implement
  readsPrec :: Read d => Int -> ReadS (SExpr d)
  readsPrec _ str =
    case parseSExpr str of
      Right res  -> [(res, "")]
      Left  _err -> []


-- ------------------------------------- See Use of `try` -------------------------------------

parserA :: Parser String
parserA = string "apple"

parserB :: Parser String
parserB = string "application"

combinedParser1 :: Parser String
combinedParser1 = parserA <|> parserB

combinedParser2 :: Parser String
combinedParser2 = try parserA <|> parserB

tryMain1 :: IO ()
tryMain1 = do
  let input = "application"
  putStrLn "Using combinedParser1:"
  case parse combinedParser1 "" input of
    Left err -> putStrLn $ "Error: " ++ show err
    Right result -> print result

  putStrLn "Using combinedParser2:"
  case parse combinedParser2 "" input of
    Left err -> putStrLn $ "Error: " ++ show err
    Right result -> print result


-- ------------------------------------- Use of A New Style -------------------------------------

-- A New Style -- firstly parse the content into a sequence of tokens 
-- and then parse the content itself.
-- This style is better than the previous one -- especially one may firstly preprocess everything

-- IN SUMMARY, THIS NEW STYLE IS NOT A GOOD IDEA -- ONE SHOULD EMPLOY A `lexing` FUNCTION
-- OF TYPE `Parser Token` TO WORK AS THE PARSER, RATHER THAN COMPUTING THE TOKEN STREAM AT THE 
-- BEGNINNING -- THERE IS FEW SUPPORT AND IT WILL BE HARDER TO DETERMINE THE POINT WHERE ERROR HAPPENED

type Lexer = Parser SExprToken

data SExprToken
  = LPAREN
  | RPAREN
  | SYMBOL !String
  deriving (Show, Eq, Ord)

skipWs :: Parser ()
skipWs = void $ many $ Parsec.satisfy isSpace

lexLParen :: Lexer
lexLParen = char '(' $> LPAREN
lexRParen :: Lexer
lexRParen = char ')' $> RPAREN
lexSymbol :: Lexer
lexSymbol = fmap SYMBOL getSingleElement

sExprLexing :: Lexer
sExprLexing = Parsec.choice [ lexLParen, lexRParen, lexSymbol ]

toTokenStream :: Parser [SExprToken]
toTokenStream = many (skipWs *> sExprLexing <* skipWs)

type TokParser = Parsec [SExprToken] ()

matchToken :: (SExprToken -> Maybe a) -> TokParser a
matchToken = tokenPrim show eIMPOSSIBLE

expectToken :: SExprToken -> TokParser ()
expectToken tok =
  matchToken (\t -> if tok == t then Just () else Nothing)

inTokParens :: TokParser a -> TokParser a
inTokParens parser = do
  expectToken LPAREN
  ret <- parser
  expectToken RPAREN
  return ret

lParen :: TokParser ()
lParen = expectToken LPAREN
rParen :: TokParser ()
rParen = expectToken RPAREN
getSym :: (Read d) => TokParser d
getSym = matchToken $ \case
  SYMBOL str ->
    case readEither str of
      Right d -> return d
      Left  m -> fail m
  _other -> Nothing

sexpr :: (Read d) => TokParser (SExpr d)
sexpr
  = try (flip SNode [] <$> getSym)
  <|>
    try (inTokParens
    (do {
      sym <- getSym;
      rest <- many sexpr;
      return $ SNode sym rest
    })
    <|>
    do {
      lst <- many sexpr;
      return $ SList lst
    }
  )


-- ------------------------------------- End of A New Style -------------------------------------

class LexTok t where
  lexing :: Parser t

