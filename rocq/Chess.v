Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Coq.Vectors.Vector.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Inductive Piece :=
  | Pawn   : Piece
  | Rook   : Piece
  | Knight : Piece
  | Bishop : Piece
  | King   : Piece
  | Queen  : Piece.

Inductive Color := Black | White.

Definition Placement := option (Color * Piece).

Definition ChessBoard := Vector.t Placement 64.

(* jww (2017-06-20): To be defined. *)
Inductive LegalBoard : ChessBoard -> Prop :=.

(* jww (2017-06-20): To be defined. *)
Inductive LegalMove : ChessBoard -> ChessBoard -> Prop :=.

Program Instance LegalMove_Reflexive : Reflexive LegalMove.
Next Obligation.
  (* jww (2017-06-20): To be defined. *)
Admitted.

Program Instance LegalMove_Transitive : Transitive LegalMove.
Next Obligation.
  (* jww (2017-06-20): To be defined. *)
Admitted.

Inductive MoveSeries (b : ChessBoard) : ChessBoard -> Set :=
  | Pass : MoveSeries b b
  | Move : forall next : ChessBoard, LegalMove b next -> MoveSeries b next.

Program Instance MoveSeries_Reflexive : Reflexive MoveSeries.
Next Obligation. apply Pass. Defined.

Program Instance MoveSeries_Transitive : Transitive MoveSeries.
Next Obligation.
  destruct H, H0.
  - reflexivity.
  - apply Move; auto.
  - apply Move; auto.
  - apply Move.
    eapply LegalMove_Transitive; eauto.
Defined.

Program Definition Chess_Category : Category := {|
  obj := ∃ b : ChessBoard, LegalBoard b;
  hom := fun x y => MoveSeries (`1 x) (`1 y);

  (* Do we consider any two move series between the same positions to be
     equivalent; or should different move series be considered distinct?

     For example, if they are distinct, then "id ∘ x ≈ x" cannot hold, since a
     game where both players pass three times is a draw, even though it
     represents the same transition as before they passed, when it was not a
     draw. *)
  homset := fun x y => {| equiv := fun f g => True |};

  id := fun x => @Pass (`1 x);
  compose := fun x y z f g =>
    @transitivity _ _ MoveSeries_Transitive _ _ _ g f
|}.

Definition StartPosition : ChessBoard.
Proof.
  (* jww (2017-06-20): To be defined. *)
Admitted.

Lemma StartPosition_Legal : LegalBoard StartPosition.
Proof.
  (* jww (2017-06-20): To be defined. *)
Admitted.

Require Export Category.Structure.Initial.

Program Instance StartPosition_Initial : Initial Chess_Category := {
  terminal_obj := (StartPosition; StartPosition_Legal)
}.
Next Obligation.
  (* jww (2017-06-20): Prove that there exist a legal series of moves from the
     starting position to any other legal position. This will require encoding
     moves in terms of how all the pieces may move, and then proceed by
     induction. *)
Admitted.
