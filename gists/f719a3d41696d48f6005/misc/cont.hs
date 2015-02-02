import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Cont

main :: IO ()
main = do
  (`runContT` return) $ do
    resume <-
      callCC $ \exit -> do
        lift $ putStrLn "Hello"
        exit $ \_ -> do
          putStrLn "World"
    lift $ putStrLn "We are here."
    lift $ resume ()