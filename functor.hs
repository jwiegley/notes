Module FunctorLaws

data Foo a = FooVal a

instance Functor Foo where
    fmap f (FooVal x) = FooVal (f x)

functorIdentity : (m : Foo a) -> fmap id m = m
functorIdentity (FooVal x) = refl
