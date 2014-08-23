Require Export Monad.

Inductive Proxy a' a b' b (m : Type -> Type) r : Type :=
  | Request : a' -> (a -> Proxy a' a b' b m r) -> Proxy a' a b' b m r
  | Respond : b -> (b' -> Proxy a' a b' b m r) -> Proxy a' a b' b m r
  | M x : (m x -> Proxy a' a b' b m r) -> Proxy a' a b' b m r
  | Pure : r -> Proxy a' a b' b m r.

Definition Producer' b m r := forall x' x, Proxy x' x unit b m r.

Definition yield {a} {m : Type -> Type} (v : a) : Producer' a m unit.
Proof.
  unfold Producer'. intros.
  apply (Respond _ _ _ _ _ _ v (Pure _ _ _ _ _ _)).
Qed.

Fixpoint go a' a b' b (m : Type -> Type) r (p : Proxy a' a b' b m r)
  r' (f : r -> r') : Proxy a' a b' b m r' :=
  match p with
  | Request a' fa  => Request _ _ _ _ _ _ a'
                      (fun x  => go _ a b' b m r (fa x) r' f)
  | Respond b  fb' => Respond _ _ _ _ _ _ b
                      (fun x => go _ a b' _ m r (fb' x) r' f)
  | M       x  mf  => M a' a b' b m r' x (fmap (fmap f) mf)
  | Pure    r      => Pure _ _ _ _ _ _ (f r)
  end.

Definition Proxy_map {a' a b' b} {m : Type -> Type} `{Applicative m} {x y}
  (f : x -> y) (p0 : Proxy a' a b' b m x) : Proxy a' a b' b m y := go p0.

Global Instance Proxy_Functor {a' a b' b} {m : b -> Set} {r} `{Functor m}
  : Functor Proxy :=
{ fmap := @Source_map M _ R
}.
Proof.
