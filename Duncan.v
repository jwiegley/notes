Definition Church (a : Type) := forall r, (a -> r -> r) -> r -> r.

Definition listR_ind : ∀ (A : Type) (P : Church A → Prop),
   P (fun _ c n => n) →
   (∀ (h : A) (t : Church A), P t → P (fun _ c n => c h (t _ c n))) →
   ∀ l : Church A, P l.
