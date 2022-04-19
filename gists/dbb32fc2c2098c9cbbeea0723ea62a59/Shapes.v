Inductive Trie (a : Type) : Shape -> Type :=
  | Unit : Trie a Bottom             (* a^0 = 1 *)
  | Id : a -> Trie a Top             (* a^1 = a *)
    (* a^(b+c) = a^b * a^c *)
  | Join {x y} : Trie a x -> Trie a y -> Trie a (Plus x y)
    (* a^(b*c) = (a^b)^c *)
  | Joins {x y} :
    (* This allows us to positively express Trie (Trie a y) x *)
    forall z, (z -> Trie a y) -> Trie z x -> Trie a (Times x y).

Arguments Unit {a}.
Arguments Id {a} _.
Arguments Join {a x y} _ _.
Arguments Joins {a x y} _ _ _.

Fixpoint vec `(x : Trie a s) : Vector.t a (size s) :=
  match x with
  | Unit         => nil a
  | Id x         => cons a x 0 (nil a)
  | Join xs ys   => vec xs ++ vec ys
  | Joins _ k xs => concat (map (vec ∘ k) (vec xs))
  end.

Program Fixpoint trie `(x : Vector.t a (size s)) : Trie a s :=
  match s with
  | Bottom    => Unit
  | Top       => Id (@hd a 0 x)
  | Plus s t  => let (ys, zs) := splitat (size s) x
                 in Join (trie ys) (trie zs)
  | Times s t => Joins (Vector.t a (size t)) trie
                       (trie (group (size s) (size t) x))
  end.

Fixpoint vec_trie `(x : Vector.t a (size s)) : vec (trie x) ~= x.
Proof.
  induction s; simpl in *.
  - now rewrite nil_inv.
  - now rewrite nil_sing.
  - destruct (splitat (size s1) x) eqn:Heqe; simpl in *.
    apply append_splitat in Heqe.
    rewrite Heqe; clear Heqe.
    rewrite IHs1.
    rewrite IHs2.
    reflexivity.
  - unfold group.
    destruct (group_dep _ _ _) eqn:Heqe; simpl in *.
    subst.
    apply concat_respects; auto.
    rewrite vec_trie.
    assert ((λ x1 : t a (size s2), vec (trie x1)) = Datatypes.id). {
      clear -vec_trie.
      extensionality w.
      now rewrite vec_trie.
    }
    rewrite H.
    now rewrite map_id.
Qed.

Theorem trie_vec `(x : Trie a s) : trie (vec x) = x.
Proof.
  induction x; simpl; auto.
  - rewrite splitat_append.
    now rewrite IHx1, IHx2.
  - unfold group.
    destruct (group_dep _ _ _) eqn:Heqe; simpl in *.
    clear Heqe.
    apply concat_inj in e; subst.
Admitted.
