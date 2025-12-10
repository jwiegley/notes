Class IFunctor (F : Type -> Type -> Type -> Type) :=
{ imap : forall {I O X Y}, (X -> Y) -> F I O X -> F I O Y
}.

Inductive IState (i o a : Type) :=
  mkIState : (i -> (a * o)) -> IState i o a.

Definition runIState {i o a} (x : IState i o a) :=
  match x with mkIState f => f end.

Definition iget  {i} : IState i i i :=
  mkIState _ _ _ (fun i => (i, i)).

Definition iput {i o} (x : o) : IState i o unit :=
  mkIState _ _ _ (fun s => (tt, x)).

Global Program Instance IState_IFunctor : IFunctor IState := {
    imap := fun _ _ _ _ f x =>
      mkIState _ _ _
               (fun st =>
                  match runIState x st with
                  | (a,st') => (f a, st')
                  end)
}.

Definition test (x : IState nat nat nat) : IState nat nat nat :=
  imap (fun n => n + 2) x.

Example test_ex : test (mkIState _ _ _ (fun s => (10, 0))) =
                        mkIState _ _ _ (fun s => (12, 0)).
Proof. reflexivity. Qed.

Class IApplicative (F : Type -> Type -> Type -> Type) :=
{ is_ifunctor :> IFunctor F

; ipure : forall {I X}, X -> F I I X
; iap : forall {I J K X Y}, F I J (X -> Y) -> F J K X -> F I K Y
}.

Global Program Instance IState_IApplicative : IApplicative IState := {
    ipure := fun _ _ x => mkIState _ _ _ (fun st => (x, st));
    iap := fun _ _ _ _ _ f x =>
      mkIState _ _ _ (fun st =>
        match runIState f st with
        | (f', st') =>
            match runIState x st' with
            | (x', st'') => (f' x', st'')
            end
        end)
}.

Class IMonad (M : Type -> Type -> Type -> Type) :=
{ is_iapplicative :> IApplicative M

; ijoin : forall {I A O X}, M I A (M A O X) -> M I O X
}.

Definition ibind {M : Type -> Type -> Type -> Type} `{IMonad M} {I J K X Y}
  (f : (X -> M J K Y)) (x : M I J X) : M I K Y :=
  @ijoin M _ I J K Y (@imap _ _ I J _ _ f x).

Global Program Instance IState_IMonad : IMonad IState := {
    ijoin := fun _ _ _ _ x => mkIState _ _ _ (fun st =>
      match runIState x st with
      | (y, st') =>
          match runIState y st' with
          | (a, st'') => (a, st'')
          end
      end)
}.

Notation "m >>>= f" := (ibind f m) (at level 25, left associativity).

Notation "X <<- A ;; B" := (A >>>= (fun X => B))
  (right associativity, at level 84, A1 at next level).

Notation "A ;;; B" := (_ <<- A ;; B)
  (right associativity, at level 84, A1 at next level).

Inductive Machine := Alpha | Beta | Gamma | Delta.

Definition shift_right : IState Machine Machine unit :=
  x <<- iget ;;
  iput (match x with
    | Alpha => Beta
    | Beta  => Gamma
    | Gamma => Delta
    | Delta => Alpha
    end).

Definition foo : IState Machine Machine unit :=
  shift_right ;;; shift_right.

Definition bar : Machine := snd (runIState foo Alpha).

Lemma bar_works : bar = Gamma.
Proof. reflexivity. Qed.

Extraction Language Haskell.

Extract Inductive Datatypes.nat => "Prelude.Int" ["0" "(Prelude.succ)"]
  "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".

Extract Inductive prod => "(,)" ["(,)"].
Extract Inductive unit => "()" [ "()" ].
Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].

Extract Inlined Constant fst => "Prelude.fst".
Extract Inlined Constant snd => "Prelude.snd".

Separate Extraction bar.