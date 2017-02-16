module Alt where

import Control.Applicative

main :: IO ()
main =
    let f x = if x == 1 then Just 4 else Nothing
        g x = if x == 3 then Just 7 else Nothing
    in print $ liftA2 (<|>) f g 5
