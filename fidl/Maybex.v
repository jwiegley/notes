Require Import Hask.Control.Monad FIDL.Tactics.

Inductive Maybe (A : Type) := Nothing | Just : A -> Maybe A.
Arguments Nothing {A}.
Arguments Just {A} _.

Definition Maybe_map `(f : X -> Y) (x : Maybe X) : Maybe Y :=
  match x with
  | Nothing => Nothing
  | Just x' => Just (f x')
  end.

Local Obligation Tactic := comp_solver.

Program Instance Maybe_Functor : Functor Maybe :=
{ fmap := @Maybe_map
}.

Definition Maybe_apply {X Y} (f : Maybe (X -> Y)) (x : Maybe X) : Maybe Y :=
  match f with
  | Nothing => Nothing
  | Just f' => match x with
    | Nothing => Nothing
    | Just x' => Just (f' x')
    end
  end.

Program Instance Maybe_Applicative : Applicative Maybe :=
{ is_functor := Maybe_Functor
; pure := @Just
; ap := @Maybe_apply
}.

Program Instance Maybe_Alternative : Alternative Maybe :=
{ empty := @Nothing
; choose := fun _ x y => match x with
                         | Nothing => y
                         | Just _ => x
                         end
}.

Definition Maybe_join {X} (x : Maybe (Maybe X)) : Maybe X :=
  match x with
  | Nothing => Nothing
  | Just Nothing => Nothing
  | Just (Just x') => Just x'
  end.

Program Instance Maybe_Monad : Monad Maybe :=
{ is_applicative := Maybe_Applicative
; join := @Maybe_join
}.
