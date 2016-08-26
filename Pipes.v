(* A stream is a function relation from positions to values. *)
Definition Stream (A : Type) := nat -> Comp A.

(* A pipe connects two bi-directional streams and produces a result after a
   number of steps. *)
Definition Pipe (A' A B' B R : Type) :=
  (A' -> Stream A) -> (B -> Stream B') -> Comp R.

Definition pipe_equiv `(x : Pipe A' A B' B R) (y : Pipe A' A B' B R) :=
  forall inc out, refineEquiv (x inc out) (y inc out).

Infix "=|=" := pipe_equiv (at level 100).

Notation "()" := (unit : Type).

Definition Void := False.

Definition Producer := Pipe Void () ().

Definition Producer' B R := forall {X' X}, Pipe X' X () B R.

Definition yield {X' X A} (x : A) : Pipe X' X () A () :=
  fun _inc out => out x 0.

Definition guard (P : Prop) : Comp () := { u : () | P }.

Definition forP `(p : Pipe x' x b' b a') `(f : b -> Pipe x' x c' c b') :
  Pipe x' x c' c a' :=
  fun inc out =>
    p inc (fun b pos => f b inc (fun c pos' => out c ??)).
