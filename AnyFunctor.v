Module AnyFunctor.

Require Import Prelude.

Set Contextual Implicit.

Definition main : IO unit :=
             undefined.

Set Implicit Arguments.

Inductive AnyFunctor ( a b : Set ) : Set :=
          | AnyFunctor : a -> (a -> b) -> AnyFunctor a b.

Unset Implicit Arguments.

Definition functorize { a b : Set } : a -> (a -> b) -> AnyFunctor a b :=
             AnyFunctor.

End AnyFunctor.

Extraction "extracted/AnyFunctor.hs" AnyFunctor.