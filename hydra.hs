import Control.Applicative
import Control.Monad.Primitive
import Data.Vector.Mutable
import Prelude hiding (read, length)

chop :: MVector (PrimState IO) Int -> Int -> IO Int
chop heads 0 = read heads 0
chop heads n = do
    count <- read heads n
    lower <- read heads (pred n)
    write heads (pred n) (lower + n * count)
    (+count) <$> chop heads (pred n)

main :: IO ()
main = do
    heads <- new 12
    set heads 0
    write heads (pred 12) 1           -- there is 1 12-headed hydra
    print =<< chop heads (pred 12)
