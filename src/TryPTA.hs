{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
module TryPTA where

import Control.Monad.Reader
import Control.Monad.ST
import Data.Vector.Mutable

data Program v e =
    PAssn v e
  | PITE e (Program v e) (Program v e)
  | PSeq (Program v e) (Program v e)
  | PProb (Program v e) (Program v e)
  | PWhile e (Program v e)
  | PNonDet (Program v e) (Program v e)

data Label v e =
    LAssn v e
  | LAssume e
  | LNonDet Int 
  | LProb Int Bool 
