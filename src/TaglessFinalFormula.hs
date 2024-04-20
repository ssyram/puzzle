module TaglessFinalFormula where

-- this file implements the Tagless-Final style Expression Problem solving methodology

class BasicVariable rep where
  vSymbol :: Int -> rep
  vConstructor :: BasicFormula f => [f] -> rep

class BasicFormula rep where
  fromVar :: (BasicVariable v) => v -> rep
  add :: rep -> rep -> rep
  mul :: rep -> rep -> rep



