Require Export
  Hask.Control.Monad
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

Definition DSL  (A B C : Type) := m A -> Comp (m B * C)%type.
Definition DSL_ (A : Type)     := Comp (m A).

Global Program Instance DSL_Functor : IFunctor DSL := {
  imap := fun I O A B f x => fmap (prod_map f) \o x
}.
Obligation 1.
  extensionality x.
  unfold id, comp, prod_map.
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

Import ApplicativeLaws.

Global Program Instance DSL_IApplicative : IApplicative DSL := {
  ipure := fun I A x s => ret (s, x);
  iap   := @dsl_ap
}.
Obligation 1.
  unfold dsl_ap, id.
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
  unfold dsl_ap, Prelude.compose, comp, id.
  extensionality rep.
  extensionality s.
  destruct s.
  simpl.
  f_equal.
  extensionality t.
  breakdown.
Admitted.
Obligation 3.
  unfold dsl_ap.
  simpl.
  extensionality rep.
  extensionality s.
  destruct s.
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
  - destruct x2.
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
  breakdown.
  - apply H1.
  - destruct x1.
    inv H2. inv H0.
    destruct x0.
    inv H3.
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
