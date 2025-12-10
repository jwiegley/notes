CoInductive stream := Cons : nat -> stream -> stream.

CoFixpoint zipWith (f : nat -> nat -> nat) (a : stream)
                   (b : stream) : stream :=
  match a, b with
    | Cons x xs, Cons y ys => Cons (f x y) (zipWith f xs ys)
  end.
