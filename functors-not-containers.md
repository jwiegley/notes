# Functors are not containers

Recentlty I was reading Dr. Bartosz's interesting article on
[Functors are Containers](http://bartoszmilewski.com/2014/01/14/functors-are-containers).
While reading it, however, something seemed a little off.  At first I thought
it was just because I'd heard the Haskell IRC channel state so often that
"Functors are not containers", but then I started to dig deeper.  This led me
to the conclusion that it makes no sense at all to equate functors with
containership, and in the following paragraphs I hope to show why.

First off, the punchline: a value of type `Maybe a` is not a functor, nor is
the type `Maybe a` a functor.  It's the *type constructor* `Maybe` which is
the functor; and how can a type constructor contain something?

I think the confusion arises from this expression:

    fmap f x
    
This is often read as "fmap maps the function f over the value x".  Thus if I
say:

    fmap (+1) (Just 10)
    
It seems like `fmap` is mapping `(+1)` over the `Just` to produce `Just 11`.
However, this is not really the most accurate way to read this expression.
Let's read it like this instead:

    (fmap (+1)) (Just 10)

And we'll read the type of `fmap` as:

    (a -> b) -> (f a -> f b)
    
Now the previous expression can be read: fmap receives a function of type `Int
-> Int`, and returns a function of type `Functor f => f Int -> f Int`.  What
is `f`?  Type inference will examine the type of `Just 10` to see that it's a
`Maybe Int`, and so unifies `f Int` with `Maybe Int`, to decide that `f` is
`Maybe`.

Next it must show that `Maybe` is a `Functor`, since `f` is required to be a
`Functor`.  So it looks up the instances of `Functor` and finds that yes,
`Maybe` is a `Functor`.  Now everything type-checks and `fmap f` can be used
to produce a new function, `f'`.  This changes the expression to:

    f' (Just 10)
    
The job of `fmap` is done, and functors are no longer involved.  The `Maybe`
instance of `Functor` was used to exchange `f` (of type `Int -> Int`) for a
function of type `Maybe Int -> Maybe Int`.  Now that function can be applied
to `Just 10`.

When put this way, it makes no sense to say that `f'` is a functor, or that
`Just 10` is a functor.  The whole action of the `Maybe` `Functor` was in
mapping `f` to `f'`.

Where, in all of this, does the idea of containment fit in?

Let's take a quick step away from Haskell, and look at the mathematical
definition of a functor, as a mapping between categories:

![Functor diagram](http://dl.dropbox.com/u/137615/Functors.png)

Where C and D are categories, and F is a natural mapping of objects and arrows
from C into D.  (It is called natural because it preserves the properties of
identity and composition of the arrows from C, yielding the so-called "functor
laws").

My question is: What can the functor F here be said to contain?  Does it
contain C, or the object and arrows of C?  Does it contain the objects and
arrows of the image of C in D?  I would think C contains its objects and
arrows, and D contains its objects and arrows, while F merely provides a way
to map to objects and arrows in D given an object or arrow in C.

This process of mapping is not a container, or a computation, or a context; it
is a simple process of identification.  It could even be modelled statically,
by making a list (on paper if you wish!), associating each object and arrow in
C with its corresponding object and arrow in D.  Would such a list be said to
"contain" anything?

As mentioned above, I think the notion of containership creeps into the
discussion because people sometimes call the objects of D functors (such as,
`Maybe Int`), when they are not functors at all.  The type constructor `Maybe`
can't contain anything any more than `F` in the above diagram "contains" what
it is mapping.

If I were to sum it all up, I'd say that `[]` is not a container, for example,
but rather a maker of types (such as `[Int]`) whose inhabitants are
containers.  But not even all functors make types whose inhabitants are
containers!
