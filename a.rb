Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.implementations.peano_naturals.
Require Import CoLoR.Util.Vector.VecUtil.

Section Ex.

  Parameter A : forall (T : Type), T -> T.

  Lemma Foo {x}: (A _ x) = x. Admitted.

  Global Instance vec_Equiv {A:Type} `{Equiv A} {n}: Equiv (vector A n)
    := Vforall2 (n:=n) equiv.

  (* @jwiegley version *)
  Global Instance Vbuild_proper {n : nat} {A:Type} `{Equiv A}:
    Proper ((forall_relation
               (fun i => pointwise_relation (i < n)%nat equiv)) ==> equiv)
           (@Vbuild A n).
  Proof.
    intros f f' E.
    unfold forall_relation, pointwise_relation in E.
    unfold equiv, vec_Equiv; apply Vforall2_intro_nth; intros j jc.
    rewrite 2!Vbuild_nth.
    apply E.
  Qed.

  Variable (CarrierA : Type).

  Parameter CarrierAe: Equiv CarrierA.

  Lemma Bar `{Equiv CarrierA}
        (i o n : nat)
        (zz : CarrierA)
        `{uf_zero: MonUnit CarrierA}
        (f u : SgOp CarrierA) :
    Vfold_left_rev f uf_zero
                   (Vbuild
                      (λ (z : nat) (zi : z < n),
                       zz)) =
    Vfold_left_rev f uf_zero
                   (Vbuild
                      (λ (z : nat) (zi : z < n),
                       A _ zz)).
  Proof.
    setoid_rewrite Foo.
  Qed.

End Ex.
