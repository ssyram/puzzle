{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Formula where

{- 
Formulas are composed with two kinds: 
1) the Environment; 
2) the Variable
-}

import Data.Function

{-| This definition is defined for general manipulation
Only put in the needed environment here, including variable constructor 
-}
data Formula env = Formula env [Formula env]

class EvalEnv env res where
  eval :: env -> [Formula env] -> res 


