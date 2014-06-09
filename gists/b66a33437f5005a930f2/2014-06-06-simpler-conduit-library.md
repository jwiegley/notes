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

We can obtain a slightly easier function type for our needs by reversing the
arguments:

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
`sourceList [1..10]` above.  (I call the closure `await`, although it's
behavior is a lot closer to a folding-variant of the `awaitForever` function
from `conduit`).  `await` wants a starting state, and a function to fold
that state over the incoming elements.

Both of these are regular, higher-order functions, so we can build a pipeline
using nothing more than function application:

``` haskell
sumC (sourceList [1..10])
```

Notice how close this is to the non-streaming version `sum (id [1..10])`; and
if we execute the pipeline using `runIdentity`, the two are identical.

## Adding type synonyms

Since the "fold closure" argument is cumbersome to restate, let's restate it
as a type synonym:

``` haskell
type Source m a r = r -> (r -> a -> m r) -> m r
```

With this synonym, the example source and sink become:

``` haskell
sourceList :: Monad m => [a] -> Source m a r
sumC :: (Num a, Monad m) => Source m a a -> m a
```

Another pattern we'll start noticing pretty shortly is that every "sink" is a
fold from a Source down to its result type.  We can capture this using another
type synonym:

``` haskell
type Sink a m r = Source m a r -> m r
```

It's not really necessary, but it advertises to the reader that we're defining
a sink.  Likewise, a "conduit" is always a mapping from one source to another
where the result type is common:

``` haskell
type Conduit a m b r = Source m a r -> Source m b r
```

In cases where the result types must differ (for example, the `dropC` function
in `simple-conduit`), we cannot use these type synonyms, but they are handy in
the majority of cases.

With these synonyms, the types of our sources and sinks should start looking
familiar to users of the regular conduit library
([mapC](http://hackage.haskell.org/package/conduit-combinators-0.2.5.2/docs/Conduit.html#v:mapC)
here is based on `conduit-combinators`):

``` haskell
sourceList :: Monad m => [a] -> Source m a r
mapC :: Monad m => (a -> b) -> Conduit a m b r
sumC :: (Num a, Monad m) => Sink a m a
```

Conduit has special operators for connecting sources with sinks, and for
mapping sources to sources.  We don't need them, since we're just applying
functions to functions, but we can define them as synonyms easily enough:

``` haskell
infixl 1 $=
($=) :: a -> (a -> b) -> b
($=) = flip ($)

infixr 2 =$
(=$) :: (a -> b) -> (b -> c) -> a -> c
(=$) = flip (.)

infixr 0 $$
($$) :: a -> (a -> b) -> b
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
type Source m a r =
    r -> (r -> a -> m (Either r r)) -> m (Either r r)
```

Once we start implementing sources and sinks, it will be much more convenient
to use `EitherT` instead of returning an `Either` value:

``` haskell
type Source m a r =
    r -> (r -> a -> EitherT r m r) -> EitherT r m r
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
presentation above such an abstraction is not possible.  However, we can
regain some of the generality with a helper function: You can turn sinks into
conduits using a new combinator, `returnC`:

``` haskell
sinkList $ returnC $ sumC $ mapC (+1) $ sourceList [1..10]
```
