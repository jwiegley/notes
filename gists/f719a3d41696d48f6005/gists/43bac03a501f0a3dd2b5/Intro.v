(** * Curried Category Theory

This book represents a formalization in Coq of Edwardk Kmett's [hask] library
for Haskell.  In it, Edward makes use of category theory to unify certain
concepts that before seemed merely related.  Much of this unification is
achieved by choosing the right category, equipped with a monoidal bifunctor of
some kind, and then currying that bifunctor to obtain a mapping from one
concept to another.  With it, many type classes which had to be implemented
separately before (e.g., [Functor], [Bifunctor], [Profunctor], [Applicative]),
can be derived from very few core definitions.
