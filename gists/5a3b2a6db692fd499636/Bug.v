Inductive T (i o a : Type) := mk : (i -> (a * o)) -> T i o a.

Extraction Language Haskell.
Extraction T.

