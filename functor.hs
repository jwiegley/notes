module FunctorLaws

data Foo a = FooVal a

instance Functor Foo where
    fmap f (FooVal x) = FooVal (f x)

functorIdentity : (m : Foo a) -> fmap id m = id
functorIdentity _ = ?fident
