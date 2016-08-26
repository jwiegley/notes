Definition foldr_spec `(f : B -> A -> A) (z : A) (s : Stream B) : Stream A :=
  LeastFixedPoint (fDom:=[nat : Type]%list)
    (fun rec pos =>
       b <- s pos;
       z' <- match pos with
             | O => ret z
             | S n => rec n
             end;
       ret (f b z')).
