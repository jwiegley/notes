Require Export
  Hask.Control.Monad.Indexed
  Hask.Data.Tuple
  FIDL.Tactics
  FIDL.Comp.

Class DSLMonad (m : Type -> Type) := {
  m_is_monad       :> Monad m;
  m_is_alternative :> Alternative m
}.

Section DSL.

Variable (m : Type -> Type).
Context `{DSLMonad m}.

Definition DSL (A B C : Type) := m A -> Comp (m B * C)%type.

Definition DSL_ (A : Type) := Comp (m A).

Global Program Instance DSL_IFunctor : IFunctor DSL := {
  imap := fun I O A B f x => fmap (prod_map f) \o x
}.
Obligation 1.
  extensionality x.
  unfold id, comp.
  extensionality s.
  breakdown.
  - destruct x1.
    apply H1.
  - apply H0.
  - destruct x0.
    constructor.
Qed.
Obligation 2.
  extensionality x.
  unfold id, comp.
  extensionality s.
  breakdown.
  - apply H1.
  - destruct x2.
    constructor.
  - apply H1.
  - destruct x1.
    constructor.
Qed.

Definition dsl_ap {I J K A B} (df : DSL I J (A -> B)) (dx : DSL J K A) :
  DSL I K B :=
  fun rep =>
    pf <- df rep;
    match pf with (rep', f) =>
      px <- dx rep';
      match px with (rep'', x) =>
        ret (rep'', f x)
      end
    end.

Global Program Instance DSL_IApplicative : IApplicative DSL := {
  ipure := fun I A x s => ret (s, x);
  iap   := @dsl_ap
}.
Obligation 1.
  unfold dsl_ap.
  extensionality dx.
  extensionality s.
  simpl.
  breakdown.
  - destruct x, x1.
    inversion H2; subst.
    apply H1.
  - apply H0.
  - destruct x.
    constructor.
Qed.
Obligation 2.
  unfold dsl_ap, Prelude.compose, comp.
  extensionality dx.
  extensionality s.
  simpl.
  destruct s.
  unfold id.
  f_equal.
  extensionality t.
  breakdown.
  - destruct x2.
    apply H1.
  - destruct x, x1, x2.
    inv H3. inv H0. inv H3. inv H0. inv H5. inv H2.
    destruct x0.
    inv H4.
    autorewrite with monad laws.
Admitted.
Obligation 3.
  unfold dsl_ap.
  extensionality dx.
  extensionality s.
  simpl.
  breakdown.
Qed.
Obligation 4.
  unfold dsl_ap.
  extensionality dx.
  extensionality s.
  simpl.
  breakdown.
  - apply H1.
  - destruct x0.
    destruct s.
    inv H2. inv H0. inv H2. inv H0. inv H4.
    destruct x0.
    inv H2. inv H3.
    constructor.
  - apply H1.
  - destruct x0.
    inv H2.
    autorewrite with monad laws.
    rewrite refine_bind_unit.
    constructor.
Qed.
Obligation 5.
  unfold dsl_ap, prod_map, comp, id.
  extensionality dx.
  extensionality s.
  simpl.
  breakdown.
  - apply H1.
  - destruct x1.
    assumption.
  - apply H1.
  - destruct x0.
    constructor.
Qed.

Close Scope monad_scope.
Close Scope imonad_scope.
Open Scope comp_scope.

Global Program Instance DSL_IMonad : IMonad DSL := {
  ijoin := fun I X O A (mm : DSL I X (DSL X O A)) rep =>
    (p <- mm rep; match p with (rep', m) => m rep' end)
}.
Obligation 1.
  unfold comp, prod_map.
  extensionality x.
  extensionality s.
  extensionality v.
  destruct v.
  breakdown.
  - apply H1.
  - destruct x2.
    inv H2. inv H0.
    destruct x1.
Admitted.
Obligation 2.
  unfold comp, prod_map, id.
  extensionality x.
  extensionality s.
  extensionality v.
  destruct v.
  breakdown.
  - destruct x3.
    inv H2.
    apply H1.
  - apply H0.
  - reflexivity.
Qed.
Obligation 3.
  unfold comp, prod_map, id.
  extensionality x.
  extensionality s.
  extensionality v.
  destruct v.
  breakdown.
Qed.
Obligation 4.
  extensionality x.
  extensionality s.
  extensionality v.
  unfold comp, prod_map, id.
  destruct v.
  rewrite refine_under_bind.
  breakdown.
  - destruct x2.
    apply H1.
  - destruct x2.
    inv H2.
    destruct x0.
    inv H0. inv H3.
Admitted.

Definition get {I} : DSL I I (m I) :=
  fun s => ret (s, s).

Definition gets `{Monad m} {I} (f : I -> m I) : DSL I I (m I) :=
  fun s => ret (s, (s >>= f)%monad).

Definition put {I O} (s : m O) : DSL I O unit :=
  fun _ => ret (s, tt).

Definition modify {I O} (f : I -> m O) : DSL I O unit :=
  fun s => ret ((s >>= f)%monad, tt).

Definition dsl_refine {I O A} (old : DSL I O A) (new : DSL I O A) :=
  forall s, refine (old s) (new s).

Notation "c ≈ v" := (dsl_refine c v) (at level 90) : dsl_scope.
Notation "'ret' X" := (pure X) (at level 81) : dsl_scope.

Open Scope dsl_scope.

Definition extend {I O} (f : I -> m O) : DSL I O unit :=
  fun s : m I => ret ((s >>= f)%monad, tt).

Definition guarded {I} (P : Prop) (f : I -> m I) : DSL I I unit :=
  fun s : m I =>
    b <- { b | decides b P };
    ret (if b then (s >>= f)%monad else s, tt).

Definition liftC {I A} (c : Comp A) : DSL I I A :=
  fun s : m I => fmap (fun x => (s, x)) c.

Notation "r <- 'get' rep ; X" := (r <- get; let r : rep := r in X)%monad
  (at level 81, right associativity, only parsing) : dsl_scope.

Definition mzero {I} : DSL I I unit :=
  fun s : m I => Return (empty, tt).

Definition guard {I} : bool -> DSL I I unit :=
  fun b (s : m I) =>
    If b
    Then Return (s, tt)
    Else Return (empty, tt).

(*
Program Definition Guard {I T} (P : Prop) (f : DSL I I T) : DSL I I T :=
  b <- liftC { b | decides b P };
  if b : bool
  then f
  else (fun _ => ret (empty, tt)).

Module DSLLaws.

Include MonadLaws.
Include TupleLaws.

Class DSLMonadLaws `{DSLMonad rep m} := {
  m_has_monad_laws       :> MonadLaws m(* ; *)
  (* m_has_alternative_laws :> AlternativeLaws m *)
}.

Program Instance DSL_FunctorLaws {rep} `{DSLMonadLaws rep m} :
  FunctorLaws (DSL rep m).
Obligation 1.
  unfold compose.
  extensionality x.
  extensionality s.
  rewrite prod_map_id.
  unfold id.
  pose proof (@fmap_id m _).
  specialize (H1 _ (Comp (rep * a))).
  replace (fun x0 : Comp (rep * a) => (v <- x0; ret v)%comp)
    with (@id (Comp (rep * a))).
    rewrite H1.
    unfold id.
    reflexivity.
  extensionality x0.
  breakdown.
Qed.
Obligation 2.
Admitted.

Lemma fmap_pure `{Monad m} : forall A B (f : A -> B) (x : A),
  (fmap[m] f) (pure[m] x) = pure[m] (f x).
Proof.
  intros.
  simpl.
  rewrite <- ap_fmap.
  apply ap_homo.
Qed.

Program Instance DSL_ApplicativeLaws {rep} `{DSLMonadLaws rep m} :
  ApplicativeLaws (DSL rep m).
Obligation 1.
  unfold dsl_ap.
  extensionality dx.
  extensionality s.
  unfold comp_join, comp_seq, compose.
  rewrite <- join_fmap_fmap_x.
  rewrite fmap_comp_x.
  rewrite fmap_comp_x.
  Set Printing All.
Admitted.

End DSLLaws.

Global Ltac because_monads' :=
  repeat (
    repeat rewrite fmap_ret;
    repeat rewrite seq_ret;
    repeat rewrite seqT_ret;
    repeat rewrite fmap_comp_x;
    repeat rewrite join_pure_x;
    simplify with monad laws
  );
  repeat rewrite fmap_ret;
  repeat rewrite seq_ret;
  repeat rewrite seqT_ret;
  repeat rewrite fmap_comp_x;
  repeat rewrite join_pure_x;
  try simplify with monad laws;
  try finish honing;
  try solve [ intuition ];
  try reflexivity;
  eauto.

Global Ltac because_monads_nosimpl := do 5 because_monads'.

Global Ltac because_monads := repeat (because_monads_nosimpl; simpl).
*)

End DSL.

Open Scope imonad_scope.

Arguments liftC {m I A} c _ _.

Definition foo `{DSLMonad m} : DSL m nat nat nat :=
  n <- liftC { n | n > 10 } ;
  _ <- guarded (n < 15) (pure \o plus 10) ;
  b <- liftC { b | decides b (n < 100) } ;
  if b : bool
  then ipure (n + 1)
  else ipure n.

Import MonadLaws.

Definition foo_refined `{H : DSLMonad m} `{@MonadLaws m (@m_is_monad m H)} :
  { f : m nat | exists n, refine (foo (pure 0)) (ret (f, n)) }.
Proof.
  eexists.
  eexists.
  unfold foo, liftC. simpl.
  simplify with monad laws.
  refine pick val 11.
    simplify with monad laws.
    refine pick val true.
      simplify with monad laws.
      refine pick val true.
        simplify with monad laws.
        unfold bind, comp.
        rewrite fmap_pure_x, join_pure_x.
        unfold id.
        reflexivity.
      constructor.
      omega.
    constructor.
    omega.
  omega.
Defined.

Eval simpl in projT1 foo_refined.

Definition foo_refined' `{H : DSLMonad m} `{@MonadLaws m (@m_is_monad m H)} :
  { f : m nat | exists n, refine (foo (pure 0)) (ret (f, n)) }.
Proof.
  eexists.
  eexists.
  unfold foo, liftC. simpl.
  simplify with monad laws.
  refine pick val 20.
    simplify with monad laws.
    refine pick val false.
      simplify with monad laws.
      refine pick val true.
        simplify with monad laws.
        unfold bind, comp.
        reflexivity.
      constructor.
      omega.
    simpl.
    omega.
  omega.
Defined.

Eval simpl in projT1 foo_refined'.