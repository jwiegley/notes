It is a little tricky. The usual haskell definition would look something like in
pseudo-Agda:

    data Free (F : Functor)(X : Set) : Set
      ret : X → Free F X
      roll : F (Free F X) → Free F X

The problem, of course, is that this definition is not strictly positive.  This
is not just a technicality: free monads do not exist in general for any functor
in predicative type theory (example: the powerset functor).

Fortunately, though, we can still recover the free monad construction for many
functors F.  The higher level of generality for which this works, as far as I
know, can be obtained by using *containers* (see for example
http://www.cs.nott.ac.uk/~txa/publ/cont-tcs.pdf‎).

I have a formalisation of containers in Agda
[here](http://paolocapriotti.com/agda-base/container.core.html) together with
some basic properties of W types and M types in HoTT.  It would be nice to build
free monads on top of this.

I'll tell you a bit about containers, in case you're not familiar with them.
The idea is simple: a container is a description of a functor.  It's a way to
define a functor without having to prove any law.  Furthermore, given a
container, it is easy to define generic-programming-like constructions on it,
simply by using the data of the container, without requiring any language
support.

The downside of containers is that they fundamentally require dependent types,
so they're not really expressible in Haskell.

So, what is a container? A (non-indexed) container is composed of two things: a
set of *shapes*, and, for every shape s, a set of *positions* for s (so the
positions form a dependent type over the shapes).

The most intuitive container is probably the one that gives you the List
functor.  The shapes for List are the natural numbers.  Given a shape (i.e. a
natural number) n, the set of positions for n is the set of n numbers {0,
... n-1}.

So the idea is that every shape represents a possible... well... shape for a
data structure.  Given a shape, its set of positions define all the "holes" in
that shape where you can plug data.

Now, every Haskell data type for which DeriveFunctor works can be expressed as a
container. Furthermore, recursive types can be expressed as fixpoints of
containers, and from that you get the notions of W types (for inductive
fixpoints) and M types (for coinductive ones).

This is all formalised in my library, where I deal directly with the more
complicated case of *indexed* containers
(www.cs.nott.ac.uk/~txa/publ/ICont.pdf). The idea is the same, though.

Now, back to free monads.  There is no way to define the free monad over a
general functor, but we can define the free monad over the functor corresponding
to a container! So let's say we have a container given by a type of shapes A :
Set, and a dependent type of positions B : A → Set.  The free monad over this
functor would look like this:

    data Free (X : Set) : Set where
      ret : X → Free X
      roll : (a : A) → (B a → Free X) → Free X

Now this is a perfectly fine strictly positive definition.  This works because
by replacing the application of the functor F to Y with Σ (a : A) (B a → Y), we
proved to the positivity checker that F is a strictly positive expression.

What are A and B in the case of pipes?  Let's consider this simplified example:

    data PipeF (U V X : Set) : Set where
      await : (U → X) → PipeF U V X
      yield : V → X → PipeF U V X

So we have a shape for awaiting and a shape for every possible value we can
yield.  Hence A = Maybe V. As for B, we have a single position when yielding
(the spot where the value goes), and a position for every possible awaited
value. Thus:

    B Nothing = U
    B (Just _) = ⊤ -- (the unit type)