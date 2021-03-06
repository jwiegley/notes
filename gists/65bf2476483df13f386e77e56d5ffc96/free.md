To refresh the reader on the notion of free monads used here: A monad in
functional programming can, with some caution, be viewed as something that
"computes" when a term of type 'm (m a)' is collapsed to 'm a'. In this way,
monads build up a composite context from a chain of computations: at each
point in the series, the context from the previous call is collapsed with the
next.

The *free monad* is a construction that satisfies the monad laws, but nothing
more: it never collapses, or performs computation. It simply builds up a
nested series of functor-shaped contexts. That is, for a given functor 'f', a
value in the free monad over that functor effectively has type 'f (f (... (f
a)))'. In the case of a regular monad, these multiple 'f' layers would be
collapsed immediately by calls to 'join', but under the free monad this
structure is preserved for later analysis and reduction. This allows the
*meaning* of the construction to be deferred until later.