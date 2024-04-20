module VariousTry where

-- try ternary operators

data Cond a = a :? a

infixl 0 ?
infixl 1 :?

(?) :: Bool -> Cond a -> a
True ? (x :? _) = x
False ? (_ :? y) = y

-- >>> test $ 2 / 3
-- "a"
test :: (Ord a, Num a) => a -> String
test x = x < 2 ? "a" :? "b"

-- -- Try the typing value

-- infixl 0 |-
-- infixl 1 :-

-- data Term v =
--     Var v
--   | Lambda v (Term v)
--   | Apply (Term v) (Term v)
--   deriving Eq

-- data Type b =
--     Base b
--   | Impl (Type b) (Type b)
--   deriving Eq

-- data HasType v b = Term v :- Type b

-- newtype TypingEnv v b = TypingEnv [(v, Type b)]

-- getType v (TypingEnv lst) = findInLst v lst
--   where
--     findInLst v [] = Nothing
--     findInLst v ((v', ty):lst) = if v == v' then return ty else findInLst v lst

-- env |- (term :- ty) =
--   case term of
--     Var v -> getType v env == return ty
--     Lambda v te -> undefined
--     Apply te te' -> undefined
