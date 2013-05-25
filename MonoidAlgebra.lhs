This article is not so much about using the Applicative type class in Haskell,
as it is about understanding where it came from, and why it works the way it
does.

> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE TemplateHaskell #-}
> {-# LANGUAGE DeriveFunctor #-}
>
> import Control.Applicative
> import Data.List

To begin our story, let's talk about algebras.  An algebra is a type, say T, a
set of operations on that type, and a set of laws concerning those operations.
One very familiar algebra is that of addition over integers, which is
sometimes written shorthand as (Int, 0, +).

The laws of this algebra are as follows:

  1. zero + x = zero
  2. x + zero = zero
  3. x + (y + z) = (x + y) + z

There are many possible algebras, but some algebras recur so commonly that
their structure is identified by name.  This particular algebraic structure is
called a "monoid".

It's important to note that it's the *structure* which a monoid, not this
particular instance of the structure over integers, zero and addition.  We can
express the generality of the structure by making our data type polymorphic
and turning it into a type class.  We'll also give the operations some
familiar names.

> class Monoid a where
>     mempty  :: a
>     mappend :: a -> a -> a

Now, that's much more general, and abstract, but we can go further.  Much
further.  First, we said initially that an algebra is a "set of operations on
a type, with laws", but `mempty` in this type class is not an operation.  We
can trivially transform it into a function which is isomorphic to a value, by
writing `() -> a`.  This gives us:

> class FunctionalMonoid a where
>     memptyF  :: () -> a
>     mappendF :: a -> a -> a

Further, in mathematics, all functions take a single argument.  Let's be more
mathy (it will help later), by transforming `mappend` into its uncurried
counterpart, `(a, a) -> `:

> class FunctionalMathyMonoid a where
>     memptyFM  :: () -> a
>     mappendFM :: (a, a) -> a

But wait, there's more!  By applying the algebra of types, any group of
functions can be reduced to a single function.  Let's do that, and I'll
explain in a minute why.  This new type class is isomorphic to the previous
one:

> class FunctionalMathyMonoid2 a where
>     algebra :: Either () (a, a) -> a

This means that the following represent the same operations:

    x `mappend` y `mappend` 0
        == algebra (Right (algebra (Right (x, y)),
                           algebra (Left ())))

A type of the form `Either () (a, a)` is also called a generalized type.  We
can write an Algebraic Data Type (ADT) to give it a specific meaning in the
type system.  The following represents the exact same type:

> data MonoidAlgebra a = MEmpty | MAppend a a deriving (Eq, Show)

The difference between an `Either` type, and a `MonoidAlgebra` type, is that
the `MonoidAlgebra` is distinguished from every other type.  This permits the
type system to know that you're only using `MonoidAlgebra` where you should
be.

Now we'll rewrite our type class yet again:

> class IsMonoidAlgebra a where
>     algebraM :: MonoidAlgebra a -> a

But we can do every better than this, by parameterizing the type class on the
type of the underlying algebra:

> class Algebra alg a where
>     eval :: alg a -> a

Let's use our functor and build a specific monoid algebra for integers over
addition:

> instance Algebra MonoidAlgebra Integer where
>     eval MEmpty = 0
>     eval (MAppend x y) = x + y

Then make sure it works as we expect:

> propAlgAdd = eval (MAppend (eval (MAppend 2 3)) (eval MEmpty))
>              == (5 :: Integer)

Next, let's make `MonoidAlgebra` into a functor:

> instance Functor MonoidAlgebra where
>     fmap _ MEmpty = MEmpty
>     fmap f (MAppend x y) = MAppend (f x) (f y)

When we combine this functor with an instance of `Algebra` for some object
(e.g., a Haskell type), we get what is called an "F-algebra".

Now, if functors map objects between categories, and natural transformations
map between functors, is there a mapping between F-algebras from one category
to another.  That is, can we take a category whose objects are monoid
F-algebras, and map it to another category of monoid F-algebras?

It turns out we can do this with a monoidal functor.  It has roughly the form:

    Functor f => f a + f b -> f (a * b)

Where f is our functor, + is an algebra over functors in the source category,
and * is the algebra of the target category.

A further step we can take is to turn our monoid algebra into a free algebra.
What this means for us that algebraic expressions persist in their unreduced
form, meaning we can represent expression trees of monoidal operations, and
evaluate them recursively at a later time.  First we have to adjust make our
data type recursive, which means we also need to add leaf nodes:

> data MonoidAlgebraF a r = MEmptyF
>                         | MValueF a
>                         | MAppendF r r
>                         deriving (Eq, Show, Functor)
>
> newtype Fix f = Fix { unFix :: f (Fix f) }
>
> cata :: Functor f => (f a -> a) -> Fix f -> a
> cata alg = alg . fmap (cata alg) . unFix
>
> instance Algebra (MonoidAlgebraF Integer) Integer where
>     eval MEmptyF        = 0
>     eval (MValueF v)    = v
>     eval (MAppendF x y) = x + y
>
> propAlgFAdd = cata eval (Fix (MAppendF
>                               (Fix (MAppendF
>                                     (Fix (MValueF (2 :: Integer)))
>                                     (Fix (MValueF 3))))
>                               (Fix MEmptyF)))
>              == (5 :: Integer)

Or, to put it another way, our `MonoidAlgebra` is a functor which can map any
type into a monoidal algebraic structure.  We can then use `fmap` to apply our
F-algebras to this structure and yield the result (This actually ties in with
the root meaning of the word "algebra" in Arabic, which is roughly "to compel
something (from something else)").
