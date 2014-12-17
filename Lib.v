Program Fixpoint dep_foldl_inv
  {A : Type} {P : A -> Prop} {R : A -> A -> Prop} {E : A -> eqType}
  (b : A) (Pb : P b) (v : seq (E b)) (n : nat) (Hn : n == size v)
  (Q : forall x : A, seq (E x)) (Hsub : subseq v (Q b))
  (F : forall (b b' : A) (Rbb' : R b b'), E b -> E b')
  (f : forall (z : A) (Pz : P z) (x : E z) (xs : seq (E z)),
         subseq (x :: xs) (Q z)
           -> { res : { z' : A | R z z' }
              | P res.1 & subseq (map (F z res.1 res.2) xs) (Q res.1) })
  {struct n} : { b' : A | P b' } :=
  match (v, n) with
  | (y :: ys, S n') =>
      match f b Pb y ys Hsub with
      | exist2 (exist b' Rbb') Pb' Hsub' =>
          let ys' := map (F b b' Rbb') ys in
          @dep_foldl_inv A P R E b' Pb' ys' n' _ Q Hsub' F f
      end
  | _ => exist P b Pb
  end.
Obligation 2.
  inversion Heq_anonymous.
  clear Heq_anonymous0.
  rewrite -H1 in Hn.
  rewrite -H0 in Hn.
  simpl in Hn.
  move: eqSS Hn => /= -> /eqP ->.
  by rewrite size_map.
Qed.
