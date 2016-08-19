Require Import Fiat.Common.ilist.
Require Import Coq.Strings.String.

Record FormatCode (ty : Type) : Type := {
  length : nat;
  show : ty -> string
}.

Definition parseFormat (s : string) :
  { n : nat & { tys : Vector.t Type n & ilist (B:=FormatCode) tys } }.
Proof.
  induction s.
    exists 0.
    exists (Vector.nil _).
    exact inil.
  destruct (Ascii.ascii_dec a "%").
    destruct IHs.
    destruct s0.
    exists (S x).
    exists (Vector.cons Type nat x x0).
    exact (icons {| length := 1; show := fun n => "number!"%string |} i).
  exact IHs.
Defined.

Definition printf {n} {tys : Vector.t Type n}
           (fmt : ilist (B:=FormatCode) tys)
           (args : ilist (B:=id) tys) : string.
Proof.
  induction tys; simpl in *.
    exact ""%string.
  destruct fmt as [fmt fmts].
  destruct args as [arg args].
  set (str := show fmt arg).
  (* apply things like length, etc *)
  exact str.
Defined.

Definition fmt :=
  Eval simpl in projT2 (projT2 (parseFormat "hello %d world")).

Example printed : printf fmt (icons 10 inil) = "number!"%string.
Proof. reflexivity. Qed.