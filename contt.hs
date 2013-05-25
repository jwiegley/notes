import Control.Monad.Interface.Cont
import Control.Monad.Interface.Try (bracket_)
import Control.Monad.IO.Class
import Control.Monad.Trans.Cont

f :: ContT (Either String String) IO String
f = do
    bracket_ (say "acquired") (say "released") (say "executed")
    () <- error "error"
    return "success"
  where
    say = liftIO . putStrLn

main :: IO ()
main = flip runContT (return . Right) f >>= print
