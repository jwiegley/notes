Require Import List.
Set Implicit Arguments.

CoInductive stream : Set :=
  | Cons : nat -> stream -> stream.

CoFixpoint zipWith (f : nat -> nat -> nat) (a : stream)
         (b : stream) : stream :=
  match a, b with
    | Cons x xs, Cons y ys => Cons (f x y) (zipWith f xs ys)
  end.

CoFixpoint tail (a : stream) := match a with Cons _ xs => xs end.

CoFixpoint fibs :=
  Cons 0 (Cons 1 (tail fibs)).

CoFixpoint fibs :=
  Cons 0 (Cons 1 (match fibs with
  | Cons x xs =>
      match xs with
      | Cons y ys => Cons (x + y) xs
      end
  end)).
