(* -*- mode: coq; coq-prog-args: ("-emacs" "-R" "." "Top") -*- *)
(* File reduced by coq-bug-finder from original input, then fCoq.Lists.List to 71 linCoq.Arith.Max 765 lines to 98 lines, then from 198 lines to 116 lines, then from 130 lines to 116 lines *)
(* coqc version 8.4pl6 (April 2016) compiled on Apr 12 2016 15:31:29 with OCaml 4.01.0
   coqtop version 8.4pl6 (April 2016) *)
Require Coq.Lists.List.
Require Coq.Arith.Max.

Module Type ATOM.

  Parameter atom : Set.

  Parameter eq_atom_dec : forall x y : atom, {x = y} + {x <> y}.

End ATOM.

Module AtomImpl : ATOM.

  Definition atom := nat.

  Definition eq_atom_dec := Peano_dec.eq_nat_dec.

End AtomImpl.

Export AtomImpl.
Export Coq.Lists.List.

Set Implicit Arguments.

Notation "x == y" := (eq_atom_dec x y) (at level 67).

Notation "x \in E" := (In x E) (at level 69).
Notation "x \notin E" := (~ In x E) (at level 69).

Section Environment.

    Variable A: Type.

    Fixpoint get (x: atom) (E: list (atom * A)) : option A :=
        match E with
        | nil => None
        | (y,v)::E => if x == y then Some v else get x E
        end.

    Definition binds x v E : Prop :=
        get x E = Some v.
Definition keys (E: list (atom * A)) : list atom.
admit.
Defined.

    Definition dom := keys.

End Environment.

Definition var := atom.
Definition fname := atom.
Definition mname := atom.
Definition cname := atom.
Parameter Object : cname.

Definition typ := cname.

Module Type GenericOverExprSig.
Parameter exp : Set.
End GenericOverExprSig.

Module Export GenericOverExpr (ModuleThatDefinesExp: GenericOverExprSig).
Import ModuleThatDefinesExp.

Definition env := (list (var * typ)).

Definition flds := (list (fname * typ)).
Definition mths := (list (mname * (typ * env * exp))).

Definition ctable := (list (cname * (cname * flds * mths))).

Inductive ok_type_ (CT:ctable) : typ -> Prop :=
| ok_obj: @ok_type_ CT Object
| ok_in_ct: forall C, C \in dom CT -> @ok_type_ CT C.

Inductive directed_ct : ctable -> Prop :=
| directed_ct_nil : directed_ct nil
| directed_ct_cons :
        forall (C D : cname) (fs : flds) (ms: mths) (ct : ctable),
        directed_ct ct ->
        C \notin (keys ct) ->
        ok_type_ ct D ->
        directed_ct ((C, (D, fs, ms)) :: ct).

Definition extends_ (CT:ctable) (C D : cname) : Prop :=
    exists fs, exists ms, binds C (D,fs,ms) CT.

Inductive sub_ (CT:ctable) : typ -> typ -> Prop :=
| sub_refl : forall t, ok_type_ CT t -> sub_ CT t t
| sub_trans : forall t1 t2 t3,
        sub_ CT t1 t2 -> sub_ CT t2 t3 -> sub_ CT t1 t3
| sub_extends : forall C D, @extends_ CT C D -> sub_ CT C D.

Theorem ClassTable_rect
    (P : cname -> Type)
    (H_obj: P Object)
    (H_ind: (forall (CT :ctable) (C D : cname) fs ms,
                ok_type_ CT D ->
                binds C (D, fs, ms) CT ->
                P D -> P C))
    : forall

             (C: cname)
             ,
    P C.
Admitted.

Lemma object_sub_top : forall CT C,
    Object \notin dom CT ->
    directed_ct CT ->
    ok_type_ CT C ->
    sub_ CT C Object.

    induction CT  using ClassTable_rect .

