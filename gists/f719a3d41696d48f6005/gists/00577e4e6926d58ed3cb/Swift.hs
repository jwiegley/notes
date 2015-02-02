module Swift where

import Control.Monad.Loops

data FooArgs = FooArgs
data Result = Result

swift :: (FooArgs -> Either Result FooArgs) -> FooArgs -> Result
swift = (either (error "impossible") id .) . iterateM_
