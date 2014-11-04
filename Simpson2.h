newtype Foo = Foo (forall a. Maybe a)

f :: Int -> Foo
f = undefined

g :: Foo -> Foo
g = undefined

h :: Int -> Foo
h = f . g
