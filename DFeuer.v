Require Import Hask.Prelude.
Require Import Hask.Data.List.

Lemma dfeuer : forall (A B : Type) (g : B -> A) (f : A -> B),
  injective f -> cancel g f -> bijective f.
Proof.
  move=> A B g f Hinj Heqe.
  pose H := inj_can_sym Heqe Hinj.
  exact: Bijective H Heqe.
Qed.

Lemma arkeet : forall (A : finType) (B : eqType) (f : A -> B),
  size (enum A) > 0 -> injective f -> exists g, cancel f g.
Proof.
  move=> A B f Hsz Hinj.
  have H := mem_image Hinj.
  specialize (H (fun x => x \in enum A)).
  pose g := (fun (x : B) =>
    let s := [seq (f x, x) | x <- enum A] in
    snd (nth (x, safe_hd (enum A) Hsz) s
             (find (fun z => x == fst z) s))).
  exists g.
  move=> x.
  elim: (enum A) => //= [y ys IHys] in H Hsz g *.
  case: ys => [|z zs] /= in IHys H Hsz g *.
    clear IHys.
    rewrite /g /=.
    case X: (x == y) in H.
      move/eqP in X.
      by rewrite X eq_refl.
    rewrite inj_eq // X /=.
    admit.
  rewrite /g /=.
  case X: (x == y) in H.
    move/eqP in X.
    by rewrite X eq_refl.
  rewrite inj_eq // X /=.
  admit.
Abort.
