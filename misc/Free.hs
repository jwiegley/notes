module Free where

import Control.Monad.Free

data Commands = Foo
              | Bar String
    deriving Show

type Program = Free ((,) Commands) ()

foo :: Program
foo = Free (Foo, Pure ())

bar :: String -> Program
bar str = Free (Bar str, Pure ())

compile :: Program -> [Commands]
compile (Pure ()) = []
compile (Free (cmd, xs)) = cmd : compile xs

main :: IO ()
main = print $ compile $ do
    foo
    bar "Hello"
    bar "world!"
