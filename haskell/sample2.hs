import Control.Monad

v :: [Integer]
v = [1, 2, 3]

f :: Integer -> Integer
f = (+10)

g :: [Integer]
g = v >>= return . f