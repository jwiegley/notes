module Challenge where

import Data.IORef

foo n i = do
    r <- newIORef n
    return $ \i -> atomicModifyIORef r (\x -> (x,x+i))
