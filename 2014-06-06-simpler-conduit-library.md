---
title: Simpler conduit library based on monadic folds
description: desc here
tags: haskell
date: [2014-06-06 Fri 19:01]
category: Haskell
---

Recently I was playing around with the core types in the `conduit` library
(attempting to change leftovers so you could only unget values you had read),
when I stumbled across a formulation of those types that lead to some
interesting simplifications.

<!--more-->

Before I jump in, let's review what any effectful streaming library should aim
to accomplish.  The basics are:

  1. Iterate over values within a structure, or produced by a computation.

  2. Cleanup resources involved in that computation once they are no longer
     needed.

  3. Allow processing to be composed nicely, forming a "pipeline" from the
     initial source to a final sink.

  4. It would be nice if any part of the pipeline could decide when to
     terminate.

What I discovered during my exploration is that all four of these requirements
can be captured using simple, monadic folds, like `foldM`. Here is the type of
`foldM`:

``` haskell
foldM :: Monad m => (a -> b -> m a) -> a -> [b] -> m a
```

We can obtain a slightly easier to use function type for what follows by
rearranging the arguments:

``` haskell
sourceList :: Monad m => [b] -> a -> (a -> b -> m a) -> m a
```

This says that given a list of elements of type `b`, `sourceList` returns a
function that knows how to generate a result type `a` from a starting value by
folding over every element of that list.  We might trivially sum lists of
integers as follows:

``` haskell
sourceList [1..10] 0 $ \acc x -> return $ acc + x
```

We can abstract our summing function into a sink that works on any source of
integers:

``` haskell
sumC :: (Num a, Monad m)
     => (a -> (a -> a -> m a) -> m a) -> m a
sumC await = await 0 $ \acc x -> return $ acc + x
```

`sumC` is a higher-order function that takes a fold closure obtained from
`sourceList [1..10` above.  (I call the closure `await`, although it's
behavior is a lot closer to a folding-variant of the `awaitForever` function
from `conduit`).  `await` wants a starting state, and a function to mutate
that state over the incoming elements.

One thing to note is that the source providing the closure does not need to
know what the state's type is.  That type is always chosen by caller, in this
case `sumC`.  RankNTypes lets us express this condition using a `forall`:

``` haskell
sumC :: (Num a, Monad m)
     => (forall r. r -> (r -> a -> m r) -> m r) -> m a
sumC await = await 0 $ \acc x -> return $ acc + x
```

We can read this type is: `sumC` accepts a function that folds over any state
type -- and then uses that function to fold over an Int.  Without the
`forall`, GHC complains that `r` cannot be unified with `Int`, because the
caller of `sumC` determines the type in that case, and we have no way of
knowing which type it will pick.

Restating the source and sink then, we have:

``` haskell
sourceList :: Monad m
           => [a] -> (forall r. r -> (r -> a -> m r) -> m r)

sumC :: (Num a, Monad m)
     => (forall r. r -> (r -> a -> m r) -> m r) -> m a
```

These are both regular, higher-order functions, so we can build our pipeline
using nothing more than function application:

``` haskell
sumC (sourceList [1..10])
```

Notice how close this is to non-streaming version `sum (id [1..10])`.  And if
we execute our pipeline using `runIdentity`, the two should be pretty much
identical.

Since this "fold closure" type is a bit cumbersome to restate everywhere,
let's stick it into a type synonym:

``` haskell
type Source m a = forall r. r -> (r -> a -> m r) -> m r
```

Note how the `Source` knows nothing about the type of state used by the fold,
and never needs to know.  Now our example source and sink become:

``` haskell
sourceList :: Monad m => [a] -> Source m a
sumC :: (Num a, Monad m) => Source m a -> m a
```

Another pattern we'll start noticing pretty shortly is that every "sink" is a
fold from a Source type down to a result type.  We can capture this using yet
another type synonym:

``` haskell
type Sink a m r = Source m a -> m r
```

It's not really necessary to do this, but it advertises to the reader that
we're defining a sink.  Likewise, a "conduit" is always a mapping from one
source to another:

``` haskell
type Conduit a m b = Source m a -> Source m b
```

With these type synonyms in place, the types of our sources and sinks should
start looking familiar to users of the regular conduit library:

``` haskell
sourceList :: Monad m => [a] -> Source m a
mapC :: Monad m => (a -> b) -> Conduit a m b
sumC :: (Num a, Monad m) => Sink a m a
```

Conduit has special operators for connecting sources with sinks, and for
mapping sources to sources.  We don't need them, since we're just applying
functions to functions, but we can define them as synonyms easily enough.
(Note that `flip ($)` and `.` cannot be used as you might expect in the first
two definitions, due to the presence of Rank-2 functions):

``` haskell
infixl 1 $=
($=) :: Monad m => Source m a -> Conduit a m b -> Source m b
l $= r = r l

infixr 2 =$
(=$) :: Monad m => Conduit a m b -> Sink b m r -> Sink a m r
l =$ r = \await -> r (l await)

infixr 0 $$
($$) :: Monad m => Source m a -> Sink a m r -> m r
($$) = flip ($)
```

We can now express the pipeline in three different ways:

``` haskell
sumC (mapC (+1) (sourceList [1..10]))

sumC $ mapC (+1) $ sourceList [1..10]

sumC $= mapC (+1) $$ sourceList [1..10]
```

This will perhaps seem more compelling if we use a file:

``` haskell
mapM_C putStrLn (sourceFile "hello.hs")
```

This action prints the contents of the given file, doing so in constant space
and without employing lazy I/O.  It handles opening and closing of the file
for us, and deals properly cleanup in the case of exceptions.

## Early termination

There is just one detail we haven't implemented yet, and that is the ability
for segments in the pipeline to abort processing early.  To encode this, we
need some short-circuiting behavior, which sounds like a job for Either:

``` haskell
type Source m a =
    forall r. r -> (r -> a -> m (Either r r)) -> m (Either r r)
```

Once we start implementing sources and sinks, it will be much more convenient
to use `EitherT` instead of returning an `Either` value:

``` haskell
type Source m a =
    forall r. r -> (r -> a -> EitherT r m r) -> EitherT r m r
```

This way the monadic action of `EitherT` provides the short-circuiting
behavior, rather than having to encode that explicitly in various places.

And that's it!  As simple as it is, this set of types is expressive enough to
implement many of the combinators from the original conduit library.  Of
course, it's not nearly as capable, but it's leaner, easier to understand the
core types, and significantly faster in some situations (computation of simple
pipelines over `Identity` on my machine were about 45% faster).

## Consumers and producers

One thing that conduit makes very easy to do is to abstract Sinks and Conduits
as Consumers, and Sources and Conduits as Producers.  Based on our
presentation above, such an abstraction is not possible.  However, we can
regain some of the generality with a helper function: You can turn sinks into
conduits by using a new combinator, `returnC`:

``` haskell
sinkList $ returnC $ sumC $ mapC (+1) $ sourceList [1..10]
```

Since conduits are mappings from sources to sources, you can already treat
them as you would a source.
