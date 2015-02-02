{-# LANGUAGE GADTs #-}

data Foo a where
    Bar :: Foo Int
    Baz :: Foo Float

main =
    let x = Bar in
    case x of
        Bar -> case x of Baz -> error "hmm"
