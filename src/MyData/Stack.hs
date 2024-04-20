module MyData.Stack where

import Data.STRef
import Control.Monad.ST
import Data.Array.ST
import Data.Maybe

newtype Stack s e = Stack {
  valStack :: STRef s [e]
}

newStack :: ST s (Stack s e)
newStack = Stack <$> newSTRef []

pushStack :: Stack s e -> e -> ST s ()
pushStack stk val = modifySTRef (valStack stk) (val:)

topStack :: Stack s a -> ST s (Maybe a)
topStack stk = listToMaybe <$> readSTRef (valStack stk)

popStack :: Stack s a -> ST s (Maybe a)
popStack stk = do
  let val = topStack stk
  modifySTRef (valStack stk) tail
  val

lenStack :: Stack s a -> ST s Int
lenStack stk = length <$> readSTRef (valStack stk)
