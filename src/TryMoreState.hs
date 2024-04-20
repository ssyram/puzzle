module TryMoreState where
import Control.Monad.State
import Utils

import qualified Dummy

data SomeType = SomeType {
    int :: !Int,
    double :: !Double
  }

type MyState a = State SomeType a

testSomeState :: MyState Int
testSomeState = do
  -- the `gets` function -- a convenient function to help getting the content
  content <- gets int
  return $ content + 1
