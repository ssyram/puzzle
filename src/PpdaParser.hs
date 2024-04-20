{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
module PpdaParser where

import Data.Text (Text, pack)
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Ratio (denominator, numerator)
import Data.List (intercalate)
import Data.Graph (path)
import System.FilePath
import System.Directory
import Control.Monad (forM, forM_)

type Parser = Parsec Void Text


whiteSpace :: Parser ()
whiteSpace = L.space space1 (L.skipLineComment "//") (L.skipBlockComment "/*" "*/")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme whiteSpace


-- A Self-Contained Megaparsec-based parser for SCFG and pPDA rules
-- Further analysis might be added based on the parsing result

newtype StkSym = StkSym String deriving Eq
newtype CtrlSt = CtrlSt String deriving Eq
data ProbExpr
  = EVar String
  | EConst Rational
  | EAdd ProbExpr ProbExpr
  | EMinus ProbExpr ProbExpr
  | EMul ProbExpr ProbExpr
  | EDiv ProbExpr ProbExpr
  deriving Eq
newtype Rule = Rule (CtrlSt, StkSym, ProbExpr, CtrlSt, [StkSym])

instance Show StkSym where show (StkSym str) = str
instance Show CtrlSt where show (CtrlSt str) = str
instance Show ProbExpr where
  show :: ProbExpr -> String
  show = showWithPrecedence 0
instance Show Rule where
  show :: Rule -> String
  show (Rule (q, x, prob, q', xs))
    | q == pBPAState = unwords
      [ show x
      , showArrow prob
      , unwords $ fmap show xs ]
    | otherwise = unwords
      [ show q
      , show x
      , showArrow prob
      , show q'
      , unwords $ fmap show xs ]
    where
      showArrow :: ProbExpr -> [Char]
      showArrow (EConst 1) = "->"
      showArrow pe         = "-(" ++ show pe ++ ")->"

showWithPrecedence :: Int -> ProbExpr -> String
showWithPrecedence p (EAdd e1 e2) =
    wrapIf (p > 6) $ showWithPrecedence 6 e1 ++ " + " ++ showWithPrecedence 6 e2
showWithPrecedence p (EMinus e1 e2) =
    wrapIf (p > 6) $ showWithPrecedence 6 e1 ++ " - " ++ showWithPrecedence 7 e2
showWithPrecedence p (EMul e1 e2) =
    wrapIf (p > 7) $ showWithPrecedence 7 e1 ++ " * " ++ showWithPrecedence 7 e2
showWithPrecedence p (EDiv e1 e2) =
    wrapIf (p > 7) $ showWithPrecedence 7 e1 ++ " / " ++ showWithPrecedence 8 e2
showWithPrecedence _ (EConst ra) =
    case denominator ra of
      1 -> show $ numerator ra
      m -> case numerator ra of
            0 -> "0"
            n -> "(" ++ show n ++ "/" ++ show m ++ ")"
showWithPrecedence _ (EVar s) = s

wrapIf :: Bool -> String -> String
wrapIf True s = "(" ++ s ++ ")"
wrapIf False s = s

pBPAState :: CtrlSt
pBPAState = CtrlSt "$"


ident :: Parser String
ident = lexeme $ do
  hd <- letterChar
  left <- many $ choice
    [ letterChar
    , char '\''
    , digitChar ]
  return $ hd : left

parCtrlSt :: Parser CtrlSt
parCtrlSt = CtrlSt <$> ident

parStkSym :: Parser StkSym
parStkSym = StkSym <$> ident

parProbExpr :: Parser ProbExpr
parProbExpr = do
    firstTerm <- parMulExpr
    rest <- many $ do
        opChar <- lexeme $ char '+' <|> char '-'
        term <- parMulExpr
        return (opChar, term)
    return $ foldl (\acc (op, term) ->
        if op == '+' then EAdd acc term else EMinus acc term)
      firstTerm
      rest

parMulExpr :: Parser ProbExpr
parMulExpr = do
    firstFactor <- parAtomExpr
    rest <- many $ do
        opChar <- lexeme $ char '*' <|> char '/'
        factor <- parAtomExpr
        return (opChar, factor)
    return $ foldl (\acc (op, fac) ->
        if op == '*' then EMul acc fac else EDiv acc fac)
      firstFactor
      rest


parAtomExpr :: Parser ProbExpr
parAtomExpr = choice $ try <$>
  [ EVar <$> ident
  , EConst . fromInteger . read <$> lexeme (some digitChar)
  , between (lexeme $ char '(') (lexeme $ char ')') parProbExpr ]

parRule :: Parser Rule
parRule = try par_pBPA <|> par_pPDA
  where
    par_pBPA = do
      x <- parStkSym
      prob <- parArrow
      xs <- many parStkSym
      parEndRule
      return $ Rule (pBPAState, x, prob, pBPAState, xs)
    par_pPDA = do
      q <- parCtrlSt
      x <- parStkSym
      prob <- parArrow
      q' <- parCtrlSt
      xs <- many parStkSym
      parEndRule
      return $ Rule (q, x, prob, q', xs)
    parArrow = choice $ try <$>
      [ do {
        lexeme $ string "->";
        return $ EConst 1
      }, do {
        lexeme $ string "-(";
        expr <- parProbExpr;
        lexeme $ string ")->";
        return expr
      }]
    parEndRule = lexeme $ char '.'

combineConst :: ProbExpr -> ProbExpr
combineConst (EVar s) = EVar s
combineConst (EConst ra) = EConst ra
combineConst (EAdd pe1 pe2) =
    let p1 = combineConst pe1
        p2 = combineConst pe2
    in case (p1, p2) of
        (EConst 0, _)                   -> p2
        (_, EConst 0)                   -> p1
        (EConst c1, EConst c2)          -> EConst (c1 + c2)
        (EConst c1, EAdd (EConst c2) p) -> EAdd (EConst $ c1 + c2) p
        _otherwise                      -> EAdd p1 p2
combineConst (EMinus pe1 pe2) =
    let p1 = combineConst pe1
        p2 = combineConst pe2
    in case (p1, p2) of
        (_, EConst 0)          -> p1
        (EConst c1, EConst c2) -> EConst (c1 - c2)
        _otherwise             -> EMinus p1 p2
combineConst (EMul pe1 pe2) =
    let p1 = combineConst pe1
        p2 = combineConst pe2
    in case (p1, p2) of
        (EConst 0, _)          -> EConst 0
        (_, EConst 0)          -> EConst 0
        (EConst 1, _)          -> p2
        (_, EConst 1)          -> p1
        (EConst c1, EConst c2) -> EConst (c1 * c2)
        _otherwise             -> EMul p1 p2
combineConst (EDiv pe1 pe2) =
    let p1 = combineConst pe1
        p2 = combineConst pe2
    in case (p1, p2) of
        (EConst 0, _)          -> EConst 0
        (_, EConst 1)          -> p1
        (EConst c1, EConst c2) ->
          if c2 /= 0
          then EConst (c1 / c2)
          else error "Division by zero"
        _otherwise             -> EDiv p1 p2


-- >>> parseRule "q X -(1/x)-> q' Y Z."
-- Right q X -(1 / x)-> q' Y Z
parseRule :: String -> Either (ParseErrorBundle Text Void) Rule
parseRule = parse parRule "rule" . pack

parName :: Parser String
parName = do
  lexeme $ string "--"
  lexeme $ manyTill anySingle newline

newtype Example = Example (String, [Rule])

parExample :: Parser Example
parExample = do
  name <- parName
  rules <- many parRule
  return $ Example (name, rules)


-- ================================ To LaTeX File ================================

class LaTeXPrint t where toLaTeX :: t -> String

instance LaTeXPrint String where
  toLaTeX :: String -> String
  toLaTeX s
    | length s == 1 = s
    | length s >  1 = "\\mathit{" ++ s ++ "}"
    | otherwise     = ""

instance LaTeXPrint StkSym where toLaTeX (StkSym s) = toLaTeX s
instance LaTeXPrint CtrlSt where toLaTeX (CtrlSt s) = toLaTeX s

instance LaTeXPrint Rule where
  toLaTeX :: Rule -> String
  toLaTeX (Rule (q, x, prob, q', xs))
    | q == pBPAState = unwords
      [ toLaTeX x
      , showArrow prob
      , intercalate " \\ " $ fmap toLaTeX xs
      , "\\\\" ]
    | otherwise = unwords
      [ toLaTeX q ++ " \\"
      , toLaTeX x
      , showArrow prob
      , toLaTeX q' ++ if null xs then "" else " \\"
      , intercalate " \\ " $ fmap toLaTeX xs
      , "\\\\" ]
    where
      showArrow (EConst 1) = "& \\to"
      showArrow pe         = "& \\xrightarrow{" ++ show pe ++ "}"

instance LaTeXPrint Example where
  toLaTeX :: Example -> String
  toLaTeX (Example (name, rules)) = unlines
    [ "\\paragraph{" ++ name ++ "} $\\,$"
    , ""
    , "\\begin{align*}"
    , init $ unlines $ fmap toLaTeX rules
    , "\\end{align*}"
    , "" ]

instance LaTeXPrint [Example] where
  toLaTeX :: [Example] -> String
  toLaTeX exs = unlines $ fmap toLaTeX exs

parseExamples :: String -> Either (ParseErrorBundle Text Void) [Example]
parseExamples = parse (many parExample) "example" . pack

toLaTeXExamples :: String -> Either (ParseErrorBundle Text Void) String
toLaTeXExamples str = toLaTeX <$> parseExamples str

fileToLaTeXExamples :: FilePath -> IO ()
fileToLaTeXExamples path = do
  str <- readFile path
  case toLaTeXExamples str of
    Left err -> print err
    Right s  -> putStrLn s





-- ================================ PTSV Model ================================

class ToPTSV t where toPTSV :: t -> String

isPbpa :: Rule -> Bool
isPbpa (Rule (q, _, _, _, _)) = q == pBPAState

getLCtrlSt (Rule (q, _, _, _, _)) = q
getLStkSym (Rule (_, x, _, _, _)) = x

instance ToPTSV Example where
  toPTSV :: Example -> String
  toPTSV (Example (name, rules)) =
    let initRule = head rules
        tyName = if isPbpa initRule then "pBPA" else "pPDA"
        kw_begin = "%BEGIN"
        kw_config = "config"
        kw_end = "%END"
        kw_rules = "rules"
    in
    init $ unlines
      [ "// " ++ name
      , ""
      , unwords [ kw_begin, tyName, kw_config ]
      , concat $
          [ "q0 := " ++ show (getLCtrlSt initRule) ++ "\n" | not $ isPbpa initRule ] ++
          [ "gamma0 := " ++ show (getLStkSym initRule) ]
      , unwords [ kw_end, tyName, kw_config]
      , ""
      , unwords [ kw_begin, tyName, kw_rules ]
      , init $ unlines $ fmap toPTSV rules
      , unwords [ kw_end, tyName, kw_rules ] ]

instance ToPTSV Rule where
  toPTSV :: Rule -> String
  toPTSV (Rule (q, x, prob, q', xs))
    | q == pBPAState = unwords
      [ show x
      , showArrow prob
      , unwords (fmap show xs) ++ "." ]
    | otherwise = unwords
      [ show q
      , show x
      , showArrow prob
      , show q'
      , unwords (fmap show xs) ++ "." ]
    where
      showArrow (EConst 1) = "->"
      showArrow pe         = "(" ++ show pe ++ ")->"

toPTSVExamples :: String -> Either (ParseErrorBundle Text Void) String
toPTSVExamples str = mapper <$> parseExamples str
  where
    mapper exs = intercalate "\n\n\n" $ fmap toPTSV exs

fileToPTSV :: FilePath -> IO ()
fileToPTSV path = do
  str <- readFile path
  case toPTSVExamples str of
    Left err -> print err
    Right s  -> putStrLn s

exampleRunExamplesToPTSVFiles :: FilePath -> IO ()
exampleRunExamplesToPTSVFiles path = do
  -- let path = "/Users/ssyram/Downloads/examples"
  str <- readFile path
  case parseExamples str of
    Left  peb -> print peb
    Right exs -> do
      let dir = takeDirectory path </> "PTSV examples"
      createDirectoryIfMissing False dir
      forM_ exs $ mapper dir
  where
    mapper dir ex@(Example (name, _)) = do
      let targetPath = dir </> name ++ ".txt"
      writeFile targetPath $ toPTSV ex
